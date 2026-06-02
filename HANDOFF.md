# lean-mm0 — Handoff

This is a working prototype Metamath-Zero backend for a Lean-flavoured
dependent type theory.  The goal: shrink the trusted base of a Lean-style
proof down to a tiny verifier — about 900 lines of trusted code (the
MM0 verifier plus a CIC axiomatisation in MM0 syntax) — while everything
else (kernel, elaborator, emitter, parser, tactics, ~7 kLoC) lives
outside the trust boundary.

## Current state

| | |
|---|---|
| Tests | **126 passing** across 4 files (7 kernel smoke + 3 emit basic + 57-test suite + 59 parser examples) |
| Total source | ~7.6 kLoC Python + 188 LoC MM0 prelude + 3542 LoC `.lean` examples (59 files) |
| Trusted base | `src/mm0_verify.py` (710 LoC) + `prelude/cic.mm0` (188 LoC) |
| Repo | 165 commits on `master`; clean working tree |
| Dev shell | `shell.nix` provides PyPy + CPython + bootstrapped `.venv` with pytest + xdist; tests in ~1.5 min on a multi-core box |
| Stock-MM0 experiment | `experiments/stock_mm0_cert/` — certifying-emitter proof-of-concept: drop our βιζ evaluator, certify against **stock MM0** instead.  Now certifies not only reductions but **whole elaborated proofs** — induction, universe-polymorphism (defs, opaque lemmas, inductives all at generic levels), modular opaque-lemma chains, and proofs *modulo* source axioms; **whole-environment certification re-typechecks all 325/325 elaborated declarations** by the 815-line stock base. `mm0_verify.py` is now legacy — moving to stock MM0 entirely (see section at end) |

## What the pipeline does

```
   .lean source text             prelude/cic.mm0     (CIC axiomatised
   (examples/*.lean)               (TRUSTED)          inside MM0)
        │                              ▲
        ▼                              │
   src/lean_parser.py                  │
   (parses to kernel AST)              │
        │                              │
        ▼                              │
   src/elaborator.py                   │
   (implicits, levels, instance        │
    synth, HOP unification, tactics)   │
        │                              │
        ▼                              │
   src/kernel.py                       │
   (CIC type checker — full β/δ/ι/ζ)   │
        │                              │
        ▼                              │
   src/emitter.py                      │
   (lowers kernel terms to MM0)        │
        │                              │
        ▼                              │
   .mm0 text  ──────────────────► src/mm0_verify.py
                                  (TRUSTED — re-checks)
                                       │
                                       ▼
                                     ✓ / ✗
```

If the verifier accepts the emitted MM0, the original Lean proof is sound
modulo the verifier and the CIC prelude.  Bugs in the parser, elaborator,
kernel, or emitter can only cause the verifier to reject — they can't
make a false statement check.

## Layout

```
lean-mm0/
├── HANDOFF.md          this file
├── README.md           project intro
├── docs/ARCHITECTURE.md  early-stage pipeline notes
├── prelude/
│   └── cic.mm0         ← TRUSTED: CIC axioms in MM0 syntax (188 LoC)
├── src/
│   ├── levels.py       universe-level algebra; LMeta for elaboration
│   ├── expr.py         CIC AST: Sort/BVar/FVar/Const/App/Lam/Pi/Let
│   │                   + Meta, Explicit, By (elaboration-only nodes)
│   ├── env.py          declaration store, instance database
│   ├── kernel.py       type-checker w/ β/δ/ζ/ι; records derivations
│   ├── inductive.py    auto-compiles non-indexed inductives
│   │                   (type former, ctors, recursor + ι rules)
│   ├── prelude_decls.py  hand-built stdlib (Nat, List, Eq, Vec, Quot,
│   │                   Sigma, Subtype, Int, Empty, Nat.le, Pred,
│   │                   Eq.symm, Eq.trans, ...)
│   ├── lean_parser.py  surface parser + tactic registry
│   ├── elaborator.py   implicit/level metas, first-order + HOP unif.,
│   │                   instance synth (backtracking), tactics
│   ├── emitter.py      kernel derivation → MM0 proof text
│   └── mm0_verify.py   ← TRUSTED: MM0 s-expression verifier (710 LoC)
├── examples/           59 .lean files (3542 LoC) that compile + verify
├── tests/
│   ├── test_kernel_smoke.py   (7 tests)
│   ├── test_emit_basic.py     (3 tests)
│   ├── suite.py               (57 tests across 14 categories)
│   └── test_parser.py         (59 .lean examples, each round-tripped)
├── scripts/
│   └── profile_test.py    cProfile a single parser test; dumps .pstats
├── shell.nix           Nix dev shell: PyPy + CPython + bootstrapped .venv
└── run_all.py          single entry point: runs all 4 test files
```

To run everything:

```bash
$ cd lean-mm0
$ python run_all.py
```

For fastest iteration, use the Nix dev shell (PyPy + xdist):

```bash
$ nix-shell
$ .venv/bin/pytest tests/ -n auto      # ~1.5 min on a multi-core box
```

Or with CPython + xdist (no Nix shell needed if you have pytest-xdist):

```bash
$ pip install pytest-xdist
$ python -m pytest tests/ -n auto      # ~4 min on a multi-core box
```

Benchmark on a 64-core box:

| Setup | Time | vs sequential |
|---|---|---|
| CPython sequential | 13:08 | 1x |
| CPython + xdist | 4:16 | 3.1x |
| **PyPy + xdist** | **1:32** | **8.5x** |

The bottleneck after parallel + PyPy is the single slowest test
(`decidable_eq_chain`, ~90s).  cProfile under CPython shows the
verifier's `_normalize` is called ~152M times during that test,
spending ~338s self-time at ~2μs per call (under cProfile overhead);
the per-call cost is already minimal, so the real win is reducing
the *number of calls* via memoization or hash-consing of `SExpr` —
which requires making the s-expression representation hashable
(lists → tuples throughout the verifier).  A profile helper is at
`scripts/profile_test.py`; pass a test function name and it dumps a
`.pstats` plus top-30 by cumulative / internal time.

Profiling cautionary tale: an early run pointed at `_uncurry`'s
`list.insert(0, …)` (116M calls, 25.8s self) as a big-looking quick
win.  Rewriting to O(n) (`append` + reverse once) — algorithmically
cleaner — turned out to be a wash in real time: avg spine length is
~2, so O(n²)→O(n) for n=2 is a negligible save.  cProfile call counts
can mislead.

## Source-side feature matrix

What the parser accepts and the elaborator handles:

### Declarations

| Form | Example | File |
|---|---|---|
| `def NAME .{lvls} (binders) : T := e` | `def id_poly.{u} {a : Sort u} (x : a) : a := x` | most |
| `theorem` (same shape as def but emitted as MM0 `opaque-def` — body verified once, not δ-unfolded at use sites; essential for non-trivial proof chains) | `theorem mul_comm (m n : Nat) : ... := ...` | nat_mul.lean |
| `axiom NAME : T` | `axiom Foo : Bar` | typeclass.lean |
| `example : T := proof` (anonymous theorem) | `example : Eq.{1} Nat 6 6 := Eq.refl _ _` | math.lean |
| `instance NAME : T := e` (registers in synth db) | `instance addNat : Add.{1} Nat := ...` | arith.lean |
| `inductive Name params : Type where \| ctor (args) : T \| ...` | full datatype declarations with auto-generated recursors | recursion.lean (indirectly) |
| `structure / class Name params : Type where (f : T) ...` | desugars to single-ctor inductive + projections | typeclass.lean |
| `class Name extends P1, P2 where ...` | each parent becomes a `toParent` field | inherit.lean |
| `infix / infixl / infixr [:prec] OP NAME` | binary infix operators with precedence; OP can be any contiguous run of `+-*<>=!` characters (lexer is greedy) so `++`, `>>=`, `<>` etc. all work as one token | arith.lean, infix_multi.lean |
| `notation:PREC "lit" var "lit" var "lit" => EXPR` | user-defined mixfix with bracket anchors.  Pattern alternates `"literal"` strings and bare placeholder ids, starts with a literal trigger.  Expansion is parsed once with placeholders as a bvar_stack; firing substitutes captured exprs.  Works for `[a, b] => Pair.mk a b`, `!x => Not x`, `<a> => List.cons a List.nil` patterns | notation_brackets.lean |

### Term forms

| Feature | Example |
|---|---|
| Pi types | `(x : T) -> U` or `T -> U` |
| forall syntax | `forall (x : T), P` |
| Lambdas | `fun (x : T) => e` (multi-binder, multi-paren) |
| Let-bindings | `let x : T := v; b` |
| Universe annotations | `Sort u`, `Type u`, `Prop`, `Sort (max u v)` |
| Const + level instantiation | `id.{1}` |
| Implicit `{a : T}` binders | parser tags, elaborator inserts metas |
| Instance-implicit `[a : T]` or `[T]` | elaborator does instance synthesis |
| `@`-syntax | `@id.{1} Nat 3` — disable implicit insertion |
| `match`/case | `match e : T with \| ... \| ...` (Nat, Bool, polymorphic List); `(motive := M)` annotation for dependent matches; indexed inductives (Eq, etc.) supported when motive is supplied AND no ctor is recursive |
| Recursive `def` via top-level `match` | structural recursion → recursor IH (Nat, List) |
| Numeric literals | `3` → `Nat.succ (Nat.succ (Nat.succ Nat.zero))` |
| `by TAC` proofs | `by rfl`, `by intro x; exact x` |
| `if c then a else b` | desugars to `@ite _ c _ a b`; needs `Decidable c` |
| `_` hole | fresh meta typed by the expected type; auto-synth if its type is a class |

### Elaboration

| Feature | Notes |
|---|---|
| First-order unification | structural, with δ-fallback and meta assignment |
| Higher-order pattern unification | Miller's fragment + constant-motive fallback |
| Implicit-argument insertion | at every application site for `{x : T}` binders |
| Universe-level metas | `id_poly 3` works without writing `.{1}`; level metas solved via type-of-meta propagation |
| Instance synthesis | backtracking search through env + local FVars; handles parametric instances like `addPair [Add α] [Add β] : Add (Pair α β)` |
| Deferred inst synthesis | inst metas wait until explicit args have pinned related metas, then synth fires |
| Class projections | `class` declarations generate projections with implicit params and inst-implicit `self` (so `Add.add x y` works) |
| Type elaboration | declaration types are themselves elaborated (so implicits in types like `length empty` get filled) |
| Bidirectional `Lam`-with-expected | propagates expected through outer Lams so inner `by` sees its goal |

### Tactics

| Tactic | Behaviour |
|---|---|
| `exact e` | elaborate `e` against the goal |
| `rfl` | if goal is `Eq α a b` with `a ≡ b`, produce `Eq.refl α a` |
| `intro x` | standalone; the seq interpreter peels a Π off the currently-focused goal (main goal, or a subgoal after focus shifts) and pushes `x` |
| `apply f` | elaborate `f`, peel its Π binders as fresh metas, unify the return type with the goal; explicit metas the unifier didn't pin become subgoals (each carrying a ctx snapshot from creation) |
| `assumption` | succeed if some local hypothesis (innermost-first) is def-equal to the goal |
| `rewrite h` / `rw h` | h : Eq α a b — replaces all syntactic occurrences of `a` in the goal with `b`; leaves the rewritten goal as a subgoal.  Also accepts `rw [h1, h2, …]` to chain rewrites — each operates on the previous's residual subgoal, so the final subgoal is the fully-rewritten goal |
| `cases h` | h : `Ind params indices` — emits a recursor app with one fresh meta per ctor as a subgoal.  Each subgoal has type `Π fields, Π ihs, goal`; user `intro`s the fields and IHs.  Non-dependent motive (goal stays G in every branch).  Indexed inductives are supported; the motive is constant over indices too — so case-splits on a proof of `Nat.le n m`-style hypothesis succeed but each branch sees the abstract original G, no index-specialisation |
| `induction h` | Like `cases h` but with a **dependent** motive — each subgoal's goal is `G[h := ctor pattern]` (specialised, not the abstract original) and each IH has type `motive(rec_field)`.  Requires `h` to be a local FVar.  For *indexed* inductives: if every index is an FVar, abstract directly; if some indices are concrete, do **index unification** — allocate a fresh FVar k_new per concrete index, replace orig in goal with k_new, wrap goal in `Π h_eq_i : Eq T_i orig_i k_new_i`, motive over k_news; after the recursor application apply `Eq.refl` for each concrete index to discharge the equality hypotheses and recover the original goal.  In each branch the user gets the h_eq hypothesis (specialised to the ctor's index pattern), which they discharge constructively (refl when the ctor's pattern matches the orig) or via no-confusion (when impossible).  Other context hypotheses depending on an abstracted index keep their original types (no auto-revert).  Subgoal-local intros chained with another `apply` and an `exact <fvar>` close correctly (the wrap is deferred until after all subgoals are solved) |
| `t1; t2; ...` | seq — focused-goal semantics: each tactic acts on the current focused goal.  Main intros are deferred until the very end so subgoal solutions can reference them as FVars; subgoal-local intros are wrapped into Lams immediately |
| `revert h` | inverse of `intro`: pulls a hypothesis intro'd earlier in the same `by` block back into the goal as a leading Π binder.  Pops the entry from ctx, closes the goal over its FVar, wraps with Π.  Refuses if a later intro depends on `h` (revert that one first).  Only works on intros, not on theorem binders |
| `simp [e1, …, en]` | iterates rewriting with both env-collected `@[simp]` lemmas and the per-call extras until no lemma fires, then tries `rfl`.  Lemmas may be universally quantified — simp peels their Π binders into fresh metas each iteration and unifies the LHS against goal subterms.  On match, instantiate metas and do the rewrite.  Bounded to 200 iterations |
| `@[simp]` on a decl | registers the decl in `env.simp_lemmas`; subsequent `simp` calls auto-include it.  Apply to `theorem`s whose conclusion is `Eq α a b` (after peeling Πs) |
| `have h : T := e` / `have h := e` | introduces an intermediate hypothesis named h of type T (proved by e) into the local context.  Type annotation is optional — without it, T is inferred from e.  Deferred-wrapped as a `Let` around the main term at end of seq, interleaved chronologically with intros (so `intro x; have h := f x; intro y; …` produces `λx. let h := f x in λy. …`) |

## Trust boundary detail

**Trusted (~898 LoC total):**

1. `src/mm0_verify.py` (710 LoC).  Parses an s-expression dialect of MM0
   (sorts, term ctors, defs, opaque-defs, builtins, axioms, theorems,
   iota rules).  Verifies forward proofs by substituting the proof's
   term arguments into an axiom/theorem's hypotheses + conclusion,
   normalising the result (βδιζ + level laws + a few builtins like
   `subst1`/`shift`), and comparing.  Iota rules drive recursor
   reduction.  `opaque-def` is like `def` but its body is *not*
   exposed for δ-expansion; the dedicated `opaque-def-typing` proof
   rule lifts a typing-of-body derivation to a typing-of-name claim,
   so the body is still checked once at definition time without being
   re-normalised at every call site.

2. `prelude/cic.mm0` (188 LoC).  Declares the syntactic categories
   (`expr`, `lvl`, `ctx`, `name`) and the inference rules of CIC as
   MM0 axioms: `ht-sort`, `ht-pi`, `ht-lam`, `ht-app`, `ht-conv`,
   `ht-let`, `de-beta`, `de-refl`, etc.

**Untrusted (everything else).**  A bug here cannot make the verifier
accept something false — only reject something true.

## What's been built (chronological)

81 commits — feature commits + HANDOFF updates interleaved:

```
383b984  Initial commit: lean-mm0 prototype
1cce7c4  Add structure inheritance, Sub class, Nat.pred to stdlib
5c4e219  List operations + first non-trivial induction proof
d2c7c9a  Eq.symm, Eq.trans in stdlib; succ_add and add_comm proofs
be3e47f  Tiny tactic monad: by rfl/exact/intro
39daebb  Handoff doc
e579ba5  apply + assumption tactics; subgoal-aware seq
2d91565  HANDOFF.md commit-hash patch-up
39389e2  Decidable + ite + if/then/else sugar; `_` holes
0071567  HANDOFF for Decidable
376402e  Real fix: intro is standalone; seq threads context through
1f53363  HANDOFF for intro/seq refactor
c05c399  (motive := M) annotation for dependent match
bcc9dc8  HANDOFF for dependent match
cbb4c96  Mid-seq intros via contextful subgoals
971dea0  HANDOFF for mid-seq intros
6ffe236  Indexed-inductive match v1 (non-recursive ctors)
1c7635b  HANDOFF for indexed-inductive match v1
474b45b  Nat lemmas: add_zero/mul_zero/mul_one/add_assoc/zero_mul/one_mul
1ca6361  HANDOFF for Nat lemmas
5380a78  rewrite tactic (rw alias)
45eb5a2  HANDOFF for rewrite
85f9ff3  nat_lemmas extended with rewrite-based proofs
f38d618  Decidable composition: And/Or/Not instances
2492f59  HANDOFF for Decidable compose
9c2310c  Nat building blocks: nat_no_confuse, succ_ne_zero, succ_inj
9071956  Nat.decEq via Nat.rec with Π-typed motive
e86a85f  HANDOFF for nat_inj + Nat.decEq
a96a3b1  Bool.decEq with no-confusion helpers
a0db3b8  HANDOFF for Bool.decEq
f236ace  Bool theory: not/and/or + not_not lemma
b05c35c  HANDOFF for bool_ops
27e631b  Nat.le lemmas: le_refl, le_trans
7b94dad  HANDOFF for nat_le + name-mangling gotcha
bf41a8e  Fix emitter name-mangling collision (escape '.' as '_d_')
f5e54a4  HANDOFF for emitter fix
282e66d  cases tactic (v1: non-recursive non-indexed)
2a9d98a  HANDOFF for cases v1
745cc0f  Nat.lt definition + Nat.lt_le composition
9be2bf2  HANDOFF for Nat.lt
bcfcd73  cases extended to recursive ctors (v2)
bef1c56  HANDOFF for cases v2
0c5cec8  cases: document v1 limitation (non-dependent motive only)
1fd1d0b  HANDOFF refresh
ba6b135  Theorem class + opaque-def in verifier; rewrite β-normalises goal
5ab3f07  Nat mul algebra (succ_mul, mul_comm, left_distrib, mul_assoc, right_distrib)
b60b6b2  HANDOFF: opaque-def + Theorem + Nat mul algebra
6569c95  induction tactic (dependent-motive cases) + examples
0ff0ce5  HANDOFF: induction tactic landed
e81603d  Defer subgoal-local intro wraps (real fix)
235fa48  Nat.le ordering lemmas (zero_le, le_succ, succ_le_succ, le_of_lt, …)
7809323  cases + induction on indexed inductives (FVar-index restriction)
af21325  revert tactic + add_comm via revert+induction
b72c7ed  List.decEq for List Nat + no-confusion helpers
4a0d5fb  Polymorphic List.decEq + match-on-inner-Lam-binder parser fix
10cdc3d  List theorems: length_map, map_append, map_compose
3d3ab7c  simp tactic (MVP): iterate rewrites with given lemmas, try rfl
d9765ce  @[simp] attribute + env-collected lemma database + unify match
d20de9c  Index unification for induction + name-based tactic-arg resolution
8ec2b9c  HANDOFF: comprehensive refresh after index-unif + simp + name-resolver
e37c491  Indexed-inductive match v2: recursive ctors (Nat.le.step, Vec.cons)
1413fe0  HANDOFF: patch chronological hash for indexed-match v2 commit
209769a  Auto-revert for `induction`: pulls dependent intros into G
55bbcdc  HANDOFF: patch chronological hash for auto-revert commit
dfd669d  Nat ordering chain: pred_le_pred → lt_irrefl → le_antisymm
0cb1459  HANDOFF: patch hash for nat ordering chain commit
7b21dbd  Nat.le_total: total order via double induction + cases on Or
db70aac  HANDOFF: refresh after le_total
07cd03f  Nat.decLe / Nat.decLt + min via if (instance synthesis works)
5eb908f  HANDOFF: refresh counts after Nat.decLe commit
f8bf1d2  have tactic: deferred Let-wrap interleaved with intros
e63900b  HANDOFF: refresh counts and chronological list after have
1f4fa62  List.mem + List.decMem: membership predicate and decidability
38df840  HANDOFF: refresh after list_mem
ccd8570  DecidableEq class + Nat instance + class-driven List.decMem_cls
8e3dce3  HANDOFF: refresh after DecidableEq commit
bcda0b8  Multi-char infix operators via greedy sym lexing
47d09ed  HANDOFF: refresh after multi-char infix commit
6b9f0b3  notation: bracket-anchored mixfix with placeholder substitution
9d73d56  HANDOFF: refresh after notation commit
8112b21  rw [h1, h2, …]: chained multi-rewrite
05a2b00  DecidableEq chain: Bool + parametric List instance
be30adb  have h := e: type-inferred form
```

### `383b984` — initial commit

The skeleton with everything that works:

- CIC kernel with full βδιζ
- Non-indexed inductive compiler (auto-generates recursors + ι)
- Indexed inductives (Vec, Eq, Nat.le hand-built with index templates)
- Quotient types as primitives with the Quot.lift ι rule
- Universe polymorphism with level algebra (max/imax)
- Backtracking instance synth + parametric instances
- Higher-order pattern unification (Case A: Miller; Case B: constant motive)
- Tiny Lean-4 surface parser
- `class`/`structure`/`instance`/`infix`/`example` keywords
- Implicit + level inference
- Operator precedence (Pratt-style)
- Anonymous `[T]` binders, `@`-syntax
- Recursive defs via top-level `match` on Nat and List
- 74 tests, 16 example .lean files

### `1cce7c4` — structure inheritance + Sub class + Nat.pred

- `class C extends P1, P2 where ...` parser support
- Generates `toP1`, `toP2` projections; child gets parents' fields inlined
- Multi-arg recursive calls in `match` (`Nat.sub_toy m k` where `m` passes through)
- `Nat.pred` in stdlib
- New examples: `inherit.lean`, `comparison.lean`

### `5c4e219` — list operations + first induction proof

- Polymorphic `map`, `append` (`list_ops.lean`)
- `zero_add (n : Nat) : 0 + n = n` by structural induction (`math.lean`)
- Fixed `_replace_rec_call` to handle arbitrary recursive-call shapes via
  an explicit `rec_arg_pos` (not just "last arg")
- Match's motive body now shifted by 1 to account for the motive's binder
- Multi-paren `fun (a : T) (b : U) => e` lambdas

### `d2c7c9a` — Eq.symm, Eq.trans, succ_add, add_comm

- `Eq.symm`, `Eq.trans` added to stdlib
- `succ_add (m n : Nat) : succ m + n = succ (m + n)` by induction
- `add_comm (m n : Nat) : m + n = n + m` — uses zero_add, succ_add,
  Eq.symm, Eq.trans, and HOP for the Eq.rec motive

### `be3e47f` — tactic monad

- `by TAC` syntax
- Three tactics: `rfl`, `exact`, `intro`
- `;`-sequencing (intro's body is the rest)
- New `By(tac_id)` AST node + tactic registry in `lean_parser`
- `_elab_lam_with_expected`: propagates expected type through outer Lams
  so tactics inside see their goal

### `e579ba5` — apply + assumption tactics

- `apply f`: elaborates `f`, peels every leading Π as a fresh meta
  (implicit / inst-implicit go to deferred synthesis; explicit ones
  are candidate subgoals), unifies the function's return type with the
  goal, returns explicit metas the unifier didn't auto-pin as subgoals
- `assumption`: walks `ctx.entries` innermost-first, returns the first
  FVar whose type is def-equal to the goal
- Tactic interpreter now returns `(term, [subgoal_meta_ids])`; `seq`
  drains the subgoal queue using subsequent `;`-chained tactics
- Top-level `by` and `intro` both error if subgoals survive their scope
  (intro's `fv` can't appear in escaping subgoal types in this prototype)
- New example `apply.lean` (7 examples)

### `39389e2` — Decidable + ite + if/then/else sugar; `_` holes

- `Not p := p → False` as a definition
- `Decidable p : Type` inductive with `isFalse (h : Not p)` and
  `isTrue (h : p)` ctors; recursor auto-generated by `compile_inductive`
- `instDecidableTrue` / `instDecidableFalse` registered as instances
- `ite.{u} {α} {c} [d : Decidable c] (t e : α) : α` built via
  `Decidable.rec`; reduces ι-wise at the kernel
- Parser sugar: `if c then t else e` ⟶ `@ite _ c _ t e`
- `_` in expression position is now a hole — the parser emits
  `Const("_", ())`, the elaborator turns it into a fresh meta typed by
  the expected type
- The args loop in `elab` queues HOLE-typed metas for instance synth
  whenever their dom is a registered class (otherwise `@f _ _` for an
  inst slot would dangle)
- New example `decidable.lean` (7 examples; includes nested ite, a
  `def choose` taking an explicit `Decidable c`, both branches verified)

### `282e66d` — cases tactic (v1)

`cases scrutinee` infers the scrutinee's inductive type, builds a
non-dependent motive, and emits the recursor application with a fresh
meta per ctor as a subgoal.  Each subgoal's type is `Π fields, goal`
— the user `intro`s the fields manually.

v1 limitations: non-recursive ctors only (recursive would need
per-rec-arg IH motive plumbing), no indexed inductives (no index
args passed yet).

`cases.lean`: Bool, Decidable (1 field), Sum (parametric) demos.

### `a96a3b1` — Bool.decEq

Decidable equality on Bool: finite (4 cases), so no recursion is
needed.  Adds `bool_no_confuse`, `true_ne_false`, `false_ne_true` as
helpers and uses nested dependent matches on both args.

### `9071956` — Nat.decEq

`Nat.decEq n m : Decidable (Eq Nat n m)`.  Written via `Nat.rec`
directly (not the match sugar) with motive
`fun n => Π m, Decidable (Eq n m)` — this lets the IH be a function
applicable to any new `m`, working around the structural-recursion
sugar's restriction that non-recursive args can't change between the
def and the recursive call.

Three ite-based sanity examples confirm the function reduces at the
kernel for both true and false cases.

Depends on `nat_inj.lean`'s `succ_inj` and `succ_ne_zero`
(commit `9c2310c`), themselves built via `Eq.rec` transports.

### `f38d618` — compositional Decidable instances

`examples/decidable_compose.lean` adds user-side `instDecidableAnd`,
`instDecidableOr`, `instDecidableNot`.  Each takes the sub-Decidable
as inst-implicit and produces the composite via nested `match` on
the Decidable scrutinees.  Registering them as `instance` lets
`if (And p q) then ... else ...` synthesise recursively through the
proposition structure.

Note: instances must have **implicit** binders for the class
parameters (not explicit) — `_try_instance` only consumes
implicit/inst-implicit prefixes, so explicit binders block unification
with the goal.

`examples/nat_lemmas.lean` was extended with `add_one`, `sym_via_rw`,
`lift_succ` (`85f9ff3`) — three small proofs demonstrating that the
`rewrite` tactic dramatically shortens what would otherwise be nested
`Eq.rec` chains.

### `5380a78` — rewrite tactic

`rewrite h` (or `rw h`) where `h : Eq α a b` replaces every
structural occurrence of `a` in the goal with `b`, leaving the
rewritten goal as a subgoal.

The built term is
```
@Eq.rec.{u, v} α b
  (fun (a' : α) (_hp : Eq α b a') => goal[a := a'])
  ?new_subgoal
  a (Eq.symm h)
```
where `v` is taken from the goal's type (inferred as `Sort v`).

A new module-level `_replace_term` does structural substitution with
proper BVar shifting when descending into binders.

`rewrite.lean`: rewrite + `apply Eq.refl` for symmetry, and a multi-
position rewrite in a Prod equality.

### `474b45b` — Nat lemmas

`examples/nat_lemmas.lean`:

- `add_zero (n) : n + 0 = n` — Eq.refl (Nat.add recurses on second arg)
- `mul_zero (n) : n * 0 = 0` — Eq.refl (same)
- `mul_one (n) : n * 1 = n` — Eq.refl (n * 1 unfolds to n + 0 unfolds to n)
- `add_assoc (a b c) : (a+b)+c = a+(b+c)` — induction on c
- `zero_mul (n) : 0 * n = 0` — induction on n, uses Eq.rec to lift IH
- `one_mul  (n) : 1 * n = n` — induction on n, uses `succ_add` and `zero_add` from math.lean (via file chaining)

The test runner now accepts multiple filenames: `_run_example("math.lean",
"nat_lemmas.lean")` so a file can build on prior files' lemmas.

### `6ffe236` — indexed-inductive match v1

`match` now supports indexed inductives (Eq, Nat.le's refl-only
slice, etc.) when:
- the user supplies `(motive := M)` (matching the recursor's
  `Π index..., scrut → Sort`), AND
- no constructor has recursive fields (the IH-motive-application
  logic doesn't yet thread per-rec-arg index expressions).

After extracting params from the scrutinee's type, the remaining
spine args become `index_args`, which get applied to the recursor
between the minors and the scrutinee — matching the recursor's
signature.

`idx_match.lean`: `my_eq_symm` and `transport` both implemented by
matching on the Eq proof.

### `cbb4c96` — mid-seq intros via contextful subgoals

Subgoals from `apply` now carry a tuple `(meta_id, ctx_snap)` where
`ctx_snap = tuple(ctx.entries)` was taken at apply-time.  The seq
interpreter has a *focused goal* (main initially, then each subgoal
in turn): each tactic acts on it.  `intro` peels the focused goal's
Π and pushes an FVar.  When focus shifts to a subgoal, ctx is
restored to the subgoal's snapshot.

The subtlety: the main goal's intros are deferred.  Pushed onto ctx
on entry, but NOT wrapped into Lams until the very end of the seq —
that way subgoal-solving terms can reference them as FVars, and one
final `close` walk at the end converts all of them to BVars
consistently.  Subgoal-local intros (from a mid-seq intro inside
subgoal drain) are wrapped immediately, because their meta's type IS
the Π that intro peeled.

`mid_seq.lean` exercises `apply f; intro k; exact k` (HO subgoal),
main-intro + subgoal-local intro combined (`constish`), and chained
intros into a nested subgoal (`deeper`).

### `c05c399` — dependent match motive

Optional `(motive := M)` annotation before the scrutinee:
```lean
match (motive := fun (k : Nat) => Eq.{1} Nat k k) n with
| Nat.zero   => Eq.refl.{1} Nat Nat.zero
| Nat.succ k => Eq.refl.{1} Nat (Nat.succ k)
```

When supplied, `_compile_match` skips the non-dependent Bool/Nat fast
paths and uses M directly as the recursor's motive.  The general-case
path already applies the motive to each field when computing IH types,
so dependent motives work without further changes.  The user is
responsible for each arm's rhs having the right `motive (Const.applied)`
type.

### `376402e` — intro is a standalone tactic; seq threads ctx

The old design had intro nest the rest of the tactic block as its body,
so `intro h; apply f; rfl; rfl` parsed as `intro("h", seq([apply, rfl,
rfl]))`.  This worked for the common case but meant subgoals from
`apply` had no consumer outside the nested body.  Other architectural
problems flowed from this: errors when intro is followed by more
tactics than its body could absorb, and no clean way to mix intros
with subgoal-draining.

The fix:

- Parser: `intro x` returns `("intro", x)` — no sub_tac.  `intro x;
  rest` parses as `seq([intro x, ...rest])`.  `_parse_tactics` threads
  `bvar_stack` so x is visible to later tactics for BVar resolution
- Elaborator: a new `_run_seq` consumes leading intros (peeling Π
  binders off the goal, pushing FVars onto ctx), then runs the first
  non-intro tactic as the "main" and uses the rest to drain its
  subgoals — all in the extended ctx.  Lams get wrapped innermost-first
  at the end
- Standalone intro outside a seq errors with a clear message
- New example `intro_seq.lean` (5 examples; multi-intro, intro+apply
  with rfl-drain, intro+apply with assumption-drain)

## Headline examples

### Real arithmetic with classes (`examples/arith.lean`)

```lean
class Add.{u} (a : Sort u) : Sort u where
  add : a -> a -> a

instance addNat : Add.{1} Nat := Add.mk.{1} Nat Nat.add

infix + Add.add

def four : Nat := 1 + 3
theorem four_eq : Eq.{1} Nat four 4 := Eq.refl.{1} Nat 4
```

This works because: parser registers `+` as a Pratt operator → `1 + 3`
parses to `Add.add 1 3` → class projection's `{α}` and `[self]` are
inferred (Nat, addNat respectively) → `Add.add` δ-expands → its body
ι-reduces against `addNat = Add.mk Nat Nat.add` → result `Nat.add 1 3`
→ verifier ι-reduces this to `4`.

### Parametric instances (`examples/parametric_inst.lean`)

```lean
class Add.{u} (a : Sort u) : Sort u where add : a -> a -> a

structure Pair.{u, v} (a : Sort u) (b : Sort v) : Sort (max u v) where
  (fst : a)
  (snd : b)

instance addNat : Add.{1} Nat := Add.mk.{1} Nat Nat.add

instance addPair.{u, v} {a : Sort u} {b : Sort v}
    [_ia : Add.{u} a] [_ib : Add.{v} b] : Add.{max u v} (Pair.{u, v} a b) :=
  Add.mk.{max u v} (Pair.{u, v} a b)
    (fun (p q : Pair.{u, v} a b) =>
       Pair.mk.{u, v} a b
         (@Add.add.{u} a _ia (Pair.fst.{u, v} a b p) (Pair.fst.{u, v} a b q))
         (@Add.add.{v} b _ib (Pair.snd.{u, v} a b p) (Pair.snd.{u, v} a b q)))

infixl:65 + Add.add

def sum_pair : Pair.{1, 1} Nat Nat := p1 + p2

theorem sum_fst : Eq.{1} Nat (Pair.fst.{1, 1} Nat Nat sum_pair) 11 :=
  Eq.refl.{1} Nat 11
```

`p1 + p2` triggers backtracking instance synth which finds `addPair`
(parameterised), which recursively synthesises two copies of `addNat`.

### Real induction (`examples/math.lean`)

```lean
def add_comm (m n : Nat) : Eq.{1} Nat (Nat.add m n) (Nat.add n m) :=
  @Nat.rec.{0}
    (fun (k : Nat) => Eq.{1} Nat (Nat.add m k) (Nat.add k m))
    (@Eq.symm.{1} Nat (Nat.add 0 m) m (zero_add m))
    (fun (k : Nat) (ih : Eq.{1} Nat (Nat.add m k) (Nat.add k m)) =>
      @Eq.trans.{1} Nat
        (Nat.add m (Nat.succ k))
        (Nat.succ (Nat.add k m))
        (Nat.add (Nat.succ k) m)
        (@Eq.rec.{1, 0} Nat (Nat.add m k)
          (fun (x : Nat) (_ : Eq.{1} Nat (Nat.add m k) x) =>
            Eq.{1} Nat (Nat.add m (Nat.succ k)) (Nat.succ x))
          (Eq.refl.{1} Nat (Nat.add m (Nat.succ k)))
          (Nat.add k m) ih)
        (@Eq.symm.{1} Nat (Nat.add (Nat.succ k) m) (Nat.succ (Nat.add k m))
          (succ_add k m)))
    n
```

The canonical first non-trivial fact about Nat addition, proved by
structural induction on `n`, using `zero_add`, `succ_add`, and rewriting
via `Eq.rec` (motive inferred by HOP).

### Tactics (`examples/tactics.lean`)

```lean
example : Eq.{1} Nat 4 4 := by rfl
example : Eq.{1} Nat (Nat.add 2 3) 5 := by rfl

def id_via_tac : Nat -> Nat := by intro x; exact x

def id_poly_via_tac.{u} {a : Sort u} : a -> a := by intro x; exact x

example : Eq.{1} Nat (@id_poly_via_tac.{1} Nat 42) 42 := by rfl
```

## What's NOT here (honest scope)

Compared to a production Lean / mathlib stack, the major missing pieces:

| Feature | Status | Why hard |
|---|---|---|
| `Decidable` / `if then else` | implemented (`Decidable.isTrue/isFalse`, `ite`, `if/then/else` sugar, `Nat.decEq`, `Bool.decEq`, monomorphic + polymorphic `List.decEq`, composition `And`/`Or`/`Not`, `Nat.decLe`/`Nat.decLt`) | — |
| `rewrite` / `rw` tactic | implemented (builds `Eq.rec` with motive abstracting LHS; β-normalises the goal so it works inside recursor minors) | — |
| `apply` tactic | implemented; subgoals carry ctx snapshots and survive intro/seq context switches | — |
| `cases` tactic | implemented (v1+v2 for non-indexed, v3 for indexed with non-dependent motive).  Real dependent index-case-analysis (with index unification) is on `induction`, not `cases` | — |
| `induction` tactic | implemented (`examples/induction.lean`, `examples/indexed_cases.lean`, `examples/index_unif.lean`, `examples/induction_auto_revert.lean`): dependent motive, IH typed at the recursive sub-term.  Works for Nat, Bool, List, **and indexed inductives like Nat.le including concrete indices via index unification**.  Subgoal-local intros chained through further `apply`s + `exact <fvar>` close correctly (wrap deferred to end-of-seq).  **Auto-reverts dependent hypotheses** (anything in focused_intros that mentions the scrutinee or its FVar indices, transitively); the user re-intros them in each branch with the specialised type.  Def/theorem binders that depend can't be auto-reverted — restructure the proof to intro them inside the `by` block first | — |
| `revert` tactic | implemented (`examples/revert.lean`) — `revert h` pulls an intro back into the goal as a leading Π.  Naturally pairs with `induction` to generalise a hypothesis before inducting on another | — |
| `simp` tactic | implemented (`examples/simp.lean`): `simp [extras]` uses env-collected `@[simp]` lemmas + extras; peels Π binders into metas; unifies LHS against goal subterms; iterates to fixpoint and tries `rfl` | No congruence rules and no simp normal-form heuristics — significant additional infra |
| Full `match` syntax in `def` (`def f \| 0 => 0 \| succ k => k`) | not implemented | needs equation compiler |
| Match on indexed inductives with recursive ctors (`Vec.cons`, `Nat.le.step`) | implemented (`examples/idx_match_rec.lean`).  IH binder is auto-wrapped after the field binders with type `motive idx_for_rec rec_field` — index values come from the recursor rule's `rec_index_templates`.  Both non-IH-using and structurally-recursive RHSs work | — |
| Mutual inductives w/ cross-recursor | partial (constructors only) | needs the "tag-encoding" pass |
| Notation/macro system | minimal (only `infix*`) | real Lean macros are a programmable language; a useful subset (mixfix `notation`) is tractable |
| Proof irrelevance | axiom in prelude; not auto-applied | needs type-aware def-eq |
| Module/`import` system | not implemented | minimal value for a prototype |
| Mathlib itself | unreachable in any chat session | depends on ~all of the above plus 1M+ LoC of Lean |

For most of these, a small first version is tractable; see "where to pick
up" below.

## Where to pick up

Pieces ordered by impact and tractability:

1. **More Nat ordering** — what's done: `le_refl`, `le_trans`
   (`nat_le.lean`); `zero_le`, `le_succ`, `le_succ_of_le`,
   `succ_le_succ`, `lt_succ_self`, `lt_succ_of_lt`, `le_of_lt`
   (`nat_le_more.lean`); `Nat.le_zero`, `Nat.not_succ_le_zero` via
   the `induction` tactic with index unification (`index_unif.lean`);
   `Nat.pred_le_pred`, `Nat.lt_irrefl`, `Nat.le_antisymm`,
   `Nat.le_total` (`nat_le_chain.lean`); `Nat.decLe`, `Nat.decLt` +
   `min` via `if` (`nat_dec_le.lean`).  Almost saturated for first-
   order Nat ordering.

2. **More Decidable instances** — `And` / `Or` / `Not`, `Nat.decEq`,
   `Bool.decEq`, mono + polymorphic `List.decEq`, `Nat.decLe`,
   `Nat.decLt`, `List.decMem`, `DecidableEq` class + `Nat` instance +
   class-driven `List.decMem_cls` (`decidable_eq.lean`) are done.
   Open: instance for `Bool` and other base types; once those exist,
   register a `DecidableEq α → DecidableEq (List α)` instance to chain
   List equality.

3. **`simp` upgrades** — current `simp` is MVP-ish: it iterates rewrites
   from an `@[simp]` database + extras, unifies LHS against goal
   subterms, tries `rfl`.  Real simp adds: congruence rules (rewrite
   inside ANY position, including binders), normal-form heuristics,
   conditional simp lemmas (lemmas with non-Eq Π binders that need
   filling), unfolding of selected defs.  Substantial, but each piece
   is bounded.

4. **Notation/macro system** — Multi-char operators (`++`, `>>=`,
   `<>`) work via greedy sym lexing.  Bracket-anchored mixfix
   `notation:max "[" a "," b "]" => Pair.mk a b` works
   (`notation_brackets.lean`).  Open: cross-file notation propagation
   (currently file-local), richer pattern features (variadic /
   repeated placeholders), precedence-aware placeholder parsing.

5. **Mutual inductives' cross-recursor** — Compile mutual `inductive`
   blocks to a single tag-discriminated inductive, generate a
   cross-recursor.  Substantial.

6. **Lean elaborator-compat layer** — Read actual `.lean` files from
   Lean 4 source by being more permissive about syntax (newlines as
   separators, more notation forms).  Real Lean files require
   elaborator features that aren't trivially in scope, but a useful
   subset is reachable.

7. **Verifier performance — hash-cons `SExpr`.**  Profile shows
   `_normalize` dominates (152M calls / ~2μs each on
   `decidable_eq_chain`); per-call cost is already low so the lever
   is reducing call count via memoization.  Memoizing `_normalize`
   needs a hashable s-expression — currently `SExpr = Union[str,
   List[SExpr]]`, lists aren't hashable.  Switching to tuples
   throughout `mm0_verify.py` would make `_normalize(e, env)` cacheable
   by `(id(e), env_version)`, but it's invasive — every place that
   constructs an `SExpr` would need to construct a tuple, and `_subst`
   / template instantiation build them imperatively.  Substantial
   refactor of the trusted base; don't undertake casually.

## Things to know when extending

- The kernel uses **locally-nameless** representation (BVars + FVars).
  `open_` substitutes BVar(0) with an FVar; `close` is the inverse.
  Both shift outer BVars appropriately — this is a correctness invariant
  that's been subtly broken twice during development; the current state
  is right but tread carefully.

- Stored types in `LocalCtx` should never contain raw BVars referring
  to context entries — they should be FVars.  Use `_resolve_bvars` in
  `elaborator.py` to convert before pushing.

- The elaborator's `MetaContext` has TWO meta dictionaries: expression
  metas and level metas.  Always `instantiate` before checking shapes;
  always `instantiate_fully` before handing a term to the kernel.

- Tests are split across 4 files for historic reasons.  `tests/suite.py`
  has the most structured coverage (with categories and a summary).
  `tests/test_parser.py` runs each `examples/*.lean` end-to-end.

- `run_all.py` is the entry point and runs everything.

- When you make changes that break tests, the failure messages tend to
  be useful — they print expected vs got for type-mismatch errors.  Add
  `ELAB_DEBUG=1` / `ELAB_DEBUG2=1` environment variables for verbose
  elaboration traces (instrumentation is currently removed but trivial
  to re-add at the `unify` and `elab` boundaries).

- The emitter escapes Lean dots as `_d_` (and other non-safe chars as
  hex `_xNN_`) in the produced MM0 symbol names.  Earlier the encoder
  collapsed both `.` and `_` into `_`, which caused collisions like
  `Foo.bar_baz` ↔ `Foo.bar.baz`; fixed in `bf41a8e`.

- The MM0 verifier's normalisation handles β, δ (via `def`), ζ, ι (via
  `iota` declarations), and level normalisation — all transitively.
  When debugging "verifier rejects", normalize the failed term to see
  what it actually reduces to.

- **`theorem` vs `def`.**  Anything written `def f := ...` is δ-reducible
  everywhere (the kernel and the verifier will unfold it).  Anything
  written `theorem f := ...` is **opaque**: the kernel/verifier never
  unfold its body at a use site; only its declared type is observable.
  This is essential for non-trivial proof chains — without it, every
  subsequent lemma re-normalises the entire chain of dependencies and
  verification cost grows super-linearly (mul_comm alone went from >25 min
  to ~5 s when its dependencies were switched to `theorem`).
  Implementation: kernel `whnf` ignores `Theorem` decls (only `Definition`
  is δ-reduced); the emitter writes `theorem` declarations as MM0
  `opaque-def` and wraps their typing proof with the verifier's new
  `opaque-def-typing` rule, which checks the body matches the opaque-def's
  stored body before lifting the typing claim from `body` to the name.

- **The `rewrite` tactic's goal is β-normalised** before structural
  search, so it works inside recursor minors where the goal looks like
  `(λk. motive k) (ctor args)` (an unreduced β-redex).  See `_beta_norm`
  in `elaborator.py`.

- **Tactic-arg BVar resolution is name-based.**  The parser threads a
  `bvar_stack` (list of names, oldest first) with each tactic so the
  elaborator can resolve identifier-BVars.  Naive positional indexing
  `ctx.entries[-(idx+1)]` breaks across induction branches because the
  parser stack accumulates intros from ALL branches but each branch's
  ctx is restored to a per-branch snapshot.  `_resolve_bvars_named`
  looks up by NAME and walks ctx innermost-first, picking the most
  recent matching entry — correct even when a name shadows itself in
  later branches.

- **Nested `match` needs parens.**  The match parser greedily consumes
  `|...` arms; a nested match inside an arm's RHS will swallow the
  surrounding match's later arms.  Workaround: wrap the inner match in
  `(...)` — once it's a parenthesised atom, arm-greedy parsing stops at
  the closing `)`.  See `examples/option_ops.lean`'s `Option.decEq` for
  the canonical example.

- **`match` on an inner-`fun`-bound variable.**  When a `match` is
  scrutinising a BVar from a `fun` binder inside the def's body (e.g.
  `fun (ys : List α) => match ys with ...`), the parser pulls the
  scrutinee's type out of an `inner_lam_types` stack that the `fun`
  parser populates on entry and pops on exit.  Earlier, the parser
  always tried to interpret a BVar scrutinee as a def binder — which
  silently worked for monomorphic types (no BVars to drift) but produced
  a wrong shifted type with BVars off by one for polymorphic ones, so
  `List.decEq` for polymorphic `α` blew up in unification with a level
  meta.  See the `inner_lam_count`/`bidx` logic in the match parser.

## Caveat

This is a research prototype written in a series of chat sessions.  It's
not optimised; some constructions are intentionally simple where a
production system would be sophisticated (no caching, no incremental
elaboration, no proper diagnostic reporting).  But the kernel is real,
the trust boundary holds, and the examples genuinely verify end-to-end.

## Stock-MM0 trusted-base experiment (later work, in `experiments/stock_mm0_cert/`)

This is a self-contained research arc (see `git log -- experiments/stock_mm0_cert/`)
that re-examines the project's core premise.  **It does not change the main
pipeline or trusted base** — it lives entirely under
`experiments/stock_mm0_cert/` and has its own `README.md`.  Per "derive, don't
document", figures (proof-node sizes, how many obligations certify) live in
script output — run `coverage_sweep.py` — not in this doc.

### The question

Our trusted base (`src/mm0_verify.py`) is really *stock MM0 + a hand-written
βδιζ / shift / subst evaluator baked into the trusted core* (`_normalize`).
That is a weaker claim than "stock MM0", whose verifier does **zero
computation** — only first-order substitution, matching, and one
proof-driven `def` unfold.  Can we drop our evaluator and **certify every
reduction** against stock MM0 instead, so the trusted base becomes a tiny,
shared, reusable checker?

A reference clone of Mario Carneiro's MM0 is at
`scientific-computing/mm0` (sibling of this repo).  Two stock checkers were
built there and are used to check everything below:
- `mm0-rs/target/release/mm0-rs` — the Rust verifier (`cargo build --release`).
- `mm0-c/mm0-c-np` — the **minimal 815-line C kernel**, built
  `gcc main.c -O2 -D NO_PARSER -o mm0-c-np`.  This is the real "tiny trusted
  base" target.

`mm0/examples/lean.mm1` (also Mario's) is a full CIC-in-stock-MM0
axiomatisation — the Rosetta Stone that proved the logic fits and showed how
each reduction becomes an explicit proof.

### What was built (all certified by mm0-rs AND mm0-c)

An **untrusted certifying emitter** that, given a CIC term, generates an
*explicit* stock-MM0 proof of a reduction our verifier discharges with a
single `de-refl`.  Two tracks:

1. **`lean.mm1` (named-binder) track** — `cert.py` / `cert_beta.py` /
   `cert_iota.py`: substitution, β, and ι certificates with abstract algebra.
   A fresh-name supply makes the α / disjoint-variable bookkeeping (which made
   hand-authoring impractical) automatic.  Hits an unwinnable α-wall on
   *concrete* numerals (mm0 ties a Π type-binder to its λ term-binder and
   won't α-rename), which motivated:

2. **`db.mm1` (de-Bruijn) track — the real path.**  A pure-axiom de-Bruijn
   CIC prelude in stock MM0 (46 axioms), mirroring `prelude/cic.mm0` but with
   `shift` / `subst1` as **provable relations** (out of the trusted base) and
   no binder names (so no α).  Driven by `db_cert.py` (a full certifying
   evaluator + typing certifier) and `induct.py` (an inductive-type
   generator).  Milestones:
   - `1+1=2` and ground recursor computations, with shift/subst proven.
   - The **core CIC typing judgment** `ht G e T` (`ht_sort`/`var`/`pi`/`lam`/
     `app`/`conv` + Nat), and a typed theorem routed through `ht_conv` that
     holds *only* via a reduction certificate.
   - **Gated ι**: `trec` gets a real type and ι requires the recursor be
     well-applied, so ι is a sound, type-preserving equality (not an untyped
     rewrite) — `db.mm1` is a sound-core trusted base.
   - A **general inductive generator** (`induct.py`): from a spec it emits the
     whole stock-MM0 axiom block (terms, shf/sub closure, typing, gated ι) and
     registers it with the certifier.  Validated by regenerating Nat's recursor
     type *verbatim* against the hand-written `db.mm1`.  Covers the full
     inductive spectrum:

     | inductive | computation | cert nodes |
     |---|---|---|
     | `Bool` | `not true = false` / `not false = true` | 90 / 90 |
     | `ListNat` | `length [0] = 1` / `length [0,0,0] = 3` | 383 / 859 |
     | `List A` (parametric) | `length (List Nat) [0,0] = 2` | 1165 |
     | `List A` (same rec, other param) | `length (List Bool) [tt] = 1` | 725 |
     | `Eq` (indexed; J eliminator) | `eqrec Nat 0 C 1 0 (refl Nat 0) = 1` | 341 |
     | `Vec` (recursive **and** indexed) | `vlength Nat [7,7] = 2` | 2581 |

   (For contrast, our `_normalize` does each of these with **1** `de-refl`.)

### Speed: stock kernel (check) vs our verifier (compute)

`bench.py` runs Church multiplication `mul Cₙ Cₙ ⟹ Cₙ²` (pure β) both ways:
our `_normalize` (computes) vs generate-then-check with `mm0-c` (no compute).

| n | result | our verifier | mm0-c check | gen (untrusted) | cert |
|---|---|---|---|---|---|
| 8  | C₆₄   | 2.5 ms | **1.2 ms** | 2.5 ms | 18 KB |
| 16 | C₂₅₆  | 18 ms  | **1.8 ms** | 16 ms  | 34 KB |
| 24 | C₅₇₆  | 72 ms  | **1.9 ms** | 61 ms  | 58 KB |
| 28 | C₇₈₄  | 87 ms  | **1.5 ms** | 97 ms  | 76 KB |
| 32 | C₁₀₂₄ | 133 ms | **1.9 ms** | 142 ms | 95 KB |

`mm0-c` checking is ~flat (startup-dominated; the proof-check is sub-ms) while
our verifier climbs — so the stock kernel is **2× → 70× faster to check** and
pulling away, *while verifying every β-step*.  Certificates are modest (tens
of KB); generation (untrusted) is comparable to computing.  The win is
**architectural**: the correctness-critical surface shrinks to a tiny, fast,
shared, soon-formally-verified kernel; the computation moves to untrusted
generation.

### Status / honest scope

The arc answers the original question **yes, for CIC's core**, reaches real source,
and now goes past reductions to **whole elaborated proofs**: a proof that uses the
induction hypothesis (`add_comm`), a **universe-polymorphic** proof (`my_eq_symm.{u}`),
and a **modular** proof chain whose cited lemmas are checked once and used by
reference — all certified against the 815-line kernel, and (a standing property of
the entire arc) **with zero changes to the trusted base** (`db.mm1` + the stock
checkers): every step is a *generated proof*, never a new axiom.

What works (each with a runnable demo under `experiments/stock_mm0_cert/`, every
certificate checked by **both** mm0-rs and the 815-line **mm0-c**, and
faithfulness-guarded by cross-checking the `db_cert` normal form against
`src/kernel.py`'s own whnf):

- **The whole inductive spectrum** — Nat, Bool, parametric List, indexed Eq (J
  eliminator), recursive-indexed Vec — via the certifier (`db_cert.py`) and the
  inductive generator (`induct.py`).
- **User inductives auto-derived from the kernel** — `bridge.register_inductive`
  reads a `class`/`structure`/`inductive`'s kernel `Inductive`/`Constructor`/
  `Recursor`, monomorphises at use-site levels, translates field/index types with
  `_expr_to_N`, and feeds `induct.generate` — so data structures (`Pair`, `Sum`,
  `And`, `True`, `False`, …) certify with **no hand-written `db.mm1` block**.
  Their projections and instances are ordinary `def`s and ride the δ path.  Field
  / index types may mention **defs** (inlined by `_whnf_delta`: δ-unfold + β, so
  the def never enters the emitted block — no ordering constraint) and **other
  user inductives** (registered via `_try_inductive_const`, whose block is emitted
  first since this runs inside the dependent's ctor loop).  This reaches
  `Decidable` (`isFalse`'s `h : Not p`, `Not := p → False`) and inheritance
  structs (`SemiRing`/`Magma`, whose fields are other structures).
- **Typeclasses / structures over `Nat`** (`arith.lean`'s `Add`/`Mul` instances,
  algebra structures, `Decidable` composition, …) — certified by **unifying** a
  recursor's bound motive level rather than converting it.  A recursor's typing
  axiom is universe-poly in `u` (`ht_rec (g)(u: lvl)`); typing one inside a `def`
  body reaches that generic `u`, which the *closed* level normaliser can't (and
  shouldn't) prove as a conversion (`leveq (lS lz) u`).  Instead `_coerce` notes
  when the expected type becomes the actual type by *instantiating* `u` and emits
  the proof bare — MM0's `ht_app` unifies the bound level var on its side, exactly
  as the hand-written Nat / generated-recursor paths already do.  (Plus: the App
  typing rule whnf's a function's type before requiring a Π, so a recursor's
  stuck result type `C @ major` is reduced.)  Fail-safe: a wrong unification
  yields a cert **both** stock checkers reject — never a false accept.
- **The kernel bridge** (`bridge.py`): translates a real `src/expr.py` term into
  the `db_cert` AST.  Covers β, ι, conversion, and:
  - **δ** (definitional unfolding) — a CIC `def d := body` is emitted as a
    stock-MM0 `def d: expr = $ body $;`, so δ rides mm0's **own** native
    def-unfold and adds **no trusted axiom** (`register_def` / `gen_def_block`).
  - **universe-polymorphic defs** by *monomorphisation* — `register_def(env,
    name, levels)` instantiates the body at concrete use-site levels
    (`inst_levels`) into a closed def; `to_db` resolves `Const(name, levels)`
    lazily.  (Level-*generic* statements, quantified over `u`, would need level
    variables in `db.mm1` — still open.)
  - **level equations** — a `leveq` semilattice-laws block in `db.mm1` +
    `deq_sort`, so `Sort (max 0 1) ≡ Sort 1` etc. certify.  (This *did* add ~13
    trusted axioms, the universe spec — unlike δ, not free.)
  - **closed `max` / `imax` in bridged terms** — the bridge's `level_to_str`
    EVALUATES a closed `max`/`imax` to its normal-form `lS`-tower (`_eval_closed_level`,
    CIC's `imax a 0 = 0` rule), so `Pair.{1,1} : Sort (max 1 1)` / `Sum.{1,1}` reach
    the certifier as `Sort 1`.  These are definitionally equal to a numeral exactly as
    the kernel treats them; evaluating in the bridge also keeps the MONO / inductive
    name tags bijective (`max 1 1` and `1` can't collide on `name_1`).  Unblocked the
    `unsup:level` cluster — `parametric_inst` (Pair projections), `notation_brackets`,
    `cases` (Sum).  No trusted-base change (db.mm1 already had `lmax`/`limax`).
  - **`let` (ζ) + poly-def-at-head** — `to_db` ζ-inlines a CIC `let x := v in b` to
    `b[v/x]` (db.mm1 has no `elet`; the kernel ζ-reduces identically, so it's sound
    for a de-refl conversion).  And `bind_env` binds the kernel `Env` up front so a
    universe-polymorphic def first met at an obligation's *head* — with no prior
    monomorphic def to have set `_ENV` as a side effect — still resolves via the lazy
    monomorphisation path.  Fixed an order-dependent latent bug (`demo.lean`'s
    `id_poly.{1} 42` failed while `double_3` right after it bridged); also unblocked
    `apply`'s `id_assn`, `mid_seq`'s `call_at_seven`, and `idx_match`'s `my_eq_symm`.
  - **nested recursor majors** — the Nat-ι branch normalises the major before
    firing succ-ι, so a *computed* major (`Nat.add (Nat.add ..) ..`) reduces.
- **The capstone**: real `examples/*.lean` driven through the *actual* pipeline
  (`src.lean_parser.elaborate` = parser→elaborator→kernel), whose `Eq A a b`
  obligations are certified by stock mm0-c.  Two routes, chosen by the real kernel:
  the **de-refl** leaves (goals holding by computation — what `Eq.refl` / `by rfl`
  discharge — over **any** bridged type `A`, not just `Nat`: Bool, lists,
  data-structure values, …) are certified by **conversion** (`prove_conv` normalises
  both sides), which is what `Eq.refl` actually proves; and the obligations that do
  **not** convert (real proofs — induction, case analysis, transport) are certified
  by **typing the whole proof term** (`ht cnil value type`).  Both are swept under
  the both-checkers invariant — the sweep is **saturated** (every `Eq` obligation in
  the elaborated corpus certifies, by one route or the other; zero skips).
- **`Eq`-in-value obligations / sort-valued nested recursors** (`bool_dec_eq.lean`
  — `Bool` decidable equality, `brec` feeding `eqrec`).  Two layers: (1) the hand-
  written `induct.EQ` declared `teq` at `Sort 1`, but the kernel `Eq` is a `Prop`
  (`Sort 0`) — fixed (`run_induct.py`'s reference updated to match).  (2) A
  sort-valued recursor inside another recursor's motive has result type
  `(motive @ major)` (a redex), not a literal sort, so the motive level `u` leaked
  into the closed normaliser and mm0-rs saw `esort u =?= (motive @ major)`.  Fixed
  **certifier-side** (no axiom redesign, contra an earlier prediction): `_coerce`'s
  recursor gating *monomorphises* the recursor type at `u := k` read off the
  motive's normalised codomain (`inst_level`/`_codomain_sort`); and `_prove_sort`
  presents `ht_conv`'s well-formedness premise as a *literal* `esort` by normalising
  a recursor-result sort.  Both checkers accept.
- **Free-variable de-refl obligations** (`freevar_demo.py`; in the sweep,
  `math.lean`'s `add m (succ n) = succ (add m n)`, plus `dep_match`/`intro_seq`'s
  `(x : T) … → Eq A k k`).  A theorem `(x₁:T₁) … (xₙ:Tₙ) → Eq A lhs rhs` that holds
  by computation but whose sides mention the *bound* variables.  Such a goal
  genuinely cannot be stated in `cnil`: a recursor's ι-gate must type the
  free-variable motive/case, and `ht g (evar i) T` is provable only when `g` holds
  the binder — so the obligation is stated in its REAL context
  `ccons Tₙ₋₁ (… (ccons T₀ cnil))` and the certifier threads that context through
  `whnf`/`prove_norm`/`prove_conv` and the recursor gates (`prove_rec_partial*`,
  which had hardcoded the empty context), grounding the free variable via
  `ht_var0`/`ht_weak`.  (The deq proof itself is context-polymorphic — every `deq_*`
  axiom leaves `g` a metavariable — so the *reduction* is unchanged; the context is
  threaded only for the ι-gates' `ht` sub-proofs.)  The worker peels the Pi
  telescope, builds the context, and runs the kernel oracle under it (binders opened
  to FVars).  `prove_ht_nat`'s closed-numeral fast path now also falls back to
  general `ht_var0` typing when a succ-ι predecessor is itself a free variable (the
  `succ n` in `add m (succ n)`, a two-binder case exercising `ht_var0` *and*
  `ht_weak`).  Both checkers accept; closed obligations are byte-identical to before
  (`cnil`), zero per-file regressions.
- **Level-generic (open-universe) de-refl obligations** (`levelgen_demo.py`; in the
  sweep, `hop.lean`'s `rewrite_refl.{u}`).  A goal quantified over a universe param
  `u` — e.g. `(α : Sort u) (x : α) → Eq α ((fun z => z) x) x`, a β-step generic over
  `u` (the demo also does a dual-universe `(fun w => x) y = x`).  The bridge renders
  an OPEN level structurally with its bound name (`Sort u` → `(esort lv_u)`,
  `level_param_name`) and the worker binds each as a `(lv_u: lvl)` theorem binder, so
  the certificate is proved GENERICALLY, once, over all `u`.  **The key finding: this
  needs NO trusted-base change** — db.mm1's `ht_sort (g)(l: lvl)` and `deq_refl (g)(e)`
  already bind a level metavariable, so an open level simply becomes a
  universally-quantified theorem binder (the exact dual of the free-variable work —
  free variables in the *level* context).  A poly *def* used at a *generic* level
  still skips (`level_to_nat` can't name a generic monomorphisation); only the goal's
  own `Sort u` is generic here.
- **Whole proof TERMS — proofs that USE the induction hypothesis** (`proofterm_demo.py`).
  A new, deeper track: instead of certifying the `de-refl` LEAVES of a proof (a
  conversion `a ≡ b`), certify an *entire proof term* by TYPING it against its stated
  type — `ht cnil <body> <type>` (`prove_ht` + a final `_coerce` to the stated type).
  This reaches real theorems, not rfl leaves.  Certified through **both** checkers:
  `zero_add` (`add 0 n = n`, `Nat.rec` whose step transports along the IH via `Eq.rec`,
  5208 nodes), `succ_add` (7960), **`add_comm` (`m + n = n + m`, double induction,
  inlining `zero_add`+`succ_add`, 29176 nodes)**, `Bool.not_not` (case analysis,
  1838), `succ_inj` (injectivity via transport, 1677), and **`my_eq_symm.{u}`
  (`Eq α a b → Eq α b a`, J on a hypothesis, LEVEL-POLYMORPHIC, 1078 nodes)**.  **No
  trusted-base change** — db.mm1's `ht` judgment, recursor typing, and gated ι were
  always there; this just *uses* them, and the free-variable / `_is_nat` robustness
  (the `trec` typing rule feeds `induct.NAT.rec_type`, which carries non-singleton Nat
  consts, so the whnf Nat-ι gate must match by NAME, not identity) make a full
  induction proof go through.  Delta-inlined helper lemmas are fine (`add_comm` inlines
  its two `def` helpers).  **Now wired into the coverage sweep** (not just demos): a
  not-convertible `Eq` obligation — one whose sides the kernel oracle says *differ*, so
  it needs a real proof — is certified by typing the decl's whole proof term
  (`coverage_worker.try_proofterm`), so `deq` leaves and `ht cnil` whole-proofs coexist
  per file and are both checked by both checkers.  The sweep's `not-convertible` skip
  class is thereby **eliminated** (it rescued `zero_add`/`succ_add`/`add_comm`/
  `Bool.not_not`/`succ_inj`/`my_eq_symm.{u}`); together with the universe-poly def /
  inductive work (below), the sweep is now **fully SATURATED** — see *still open*.
- **Universe-polymorphic generated inductives** (the enabler for `my_eq_symm.{u}`).
  `induct.generate` now AUTO-DETECTS the level variables in each generated type and
  binds them on the typing axioms: `ht_<tycon> (g)(v: lvl)`, `ht_<ctor> (g)(v: lvl)`,
  `ht_<rec> (g)(u v: lvl)` (`u` = the recursor's motive level, always; `v` = the
  inductive's own param).  `Eq` is now genuinely universe-poly (`teq : Π A:Sort v …`,
  was the monomorphic `Sort 1`), so `Eq.{1}` and a generic `Eq.{u}` typecheck against
  the SAME axioms — MM0 unifies the level at each use site, exactly as for the
  recursor's motive.  The iota axioms are level-agnostic (params are `expr` vars), so
  they're unchanged.  **No trusted-base change** (the binder is on the generated block,
  which is itself emitted + checked); monomorphic inductives (Bool/List/Vec, closed
  `lz`/`lS` Sorts) detect no level vars → byte-identical output, sweep unchanged at 136.
- **Opaque-lemma references — modular proofs that scale** (`opaque_demo.py`).  A
  `theorem` is opaque (the kernel never δ-unfolds it — that is *how* a real proof chain
  stays cheap: each lemma is checked once, not re-normalised at every call site).  The
  proof-term track now mirrors this: a cited lemma is emitted as an mm0 `def` plus a
  `htop_<name> (g: ctx): ht g <body> <type>` theorem proved **once**, and every use
  types **by reference** to it (`prove_ht` returns `(htop_<name>)`, never re-typing the
  body).  Measured: `zadd` (`add 0 n = n`) is typed once at 5208 nodes, and a proof
  citing it *twice* (via `Eq.trans`) is 3740 nodes — *not* the ~10416 of two inlined
  copies.  **No trusted axiom**: the lemma's typing is *proved*, not asserted (a naive
  `ht g L T` axiom would be unsound — untyped `deq` makes subject-conversion fail); the
  key is that a closed body's typing proof is **context-polymorphic**, so the single
  `htop` theorem is valid in any context.  This is the stock-MM0 analogue of the
  production verifier's opaque-def-typing rule, reached with the pieces already in
  db.mm1.  (`bridge.register_opaque`; both workers emit `gen_opaque_block`.)
- **Universe-polymorphic opaque lemmas** (`poly_opaque_demo.py`, `poly_opaque_gen_demo.py`).
  A poly `theorem` cited by reference, two cases.  (a) at a **concrete** level
  (`my_eq_symm.{1}`) — MONOMORPHISED, exactly as a poly *def* is: body/type
  level-instantiated into a closed term, registered as a distinct closed opaque lemma
  per level-tag (`my_eq_symm_1`), riding every closed-opaque path unchanged.  (b) at a
  **generic** level inside *another* poly proof (`symm_symm.{u}` citing `my_eq_symm.{u}`)
  — the lemma can never be monomorphised, so its typing is proved **once, generically
  over all universes**, and referenced.  This is the exact **dual, for levels**, of the
  opacity trick: a closed body's typing is context-polymorphic (`g` a metavariable) so
  one `htop (g: ctx)` serves every site; a *generic* body's typing is in addition
  **level-polymorphic** (db.mm1's `ht_sort`/`deq_refl` already bind a level metavariable),
  so the same `prove_ht` proof, with `(lv_u: lvl)` bound on the htop, types it at every
  use level.  Mechanism: a new `OpaqueRef(san, lvls)` db_cert node (an mm0 def
  *application* of the level args, `(my_eq_symm_g lv_u)` — not a CIC eapp); the def and
  `htop` carry `(lv_u: lvl)` binders and the htop is stated over the *folded* reference
  so use sites unify the levels syntactically.  **No trusted axiom, no trusted-base
  change** — db.mm1 byte-identical; the level binder lives on the generated def/htop,
  checked like everything else.  Certified by **both** checkers (`symm_symm.{u}` 348
  nodes; the lemma typed once at 1078, cited twice by reference).
- **Universe-polymorphic `def` used at a generic level** (`poly_def_gen_demo.py`).  The
  *transparent* sibling of the poly opaque lemma: a poly `def` (`Eq.symm.{u}` via
  `apply`/`rewrite`/`rw`) used at a generic level is registered ONCE as a level-bound
  mm0 def `<name>_g (lv_u: lvl)`, and a use is a new `DefRef(san, lvls)` db_cert node →
  `(name_g lv_u)`.  **Unlike `OpaqueRef`** (opaque — typed once by an htop reference,
  never unfolds), a `DefRef` **δ-unfolds** to `body[lvls]` in `whnf`/`prove_ht` (typed
  via the unfolded body; MM0 delta-matches the folded ref), shift/subst-invariant like
  any closed def; `gen_def_block` emits the `(lv: lvl)` binders (`DEFS_LVLS`).  This is
  why a def costs more than its opaque twin (typing inlines per use): `use_sym.{u}` 2796
  nodes vs 348 for the opaque version typed once.  No trusted-base change.
- **Universe-polymorphic inductive used at a generic level** (`poly_ind_gen_demo.py`).
  The third leg, and the cleanest: an inductive's **term constructors are already
  level-agnostic** in db.mm1 (the level rides the generated typing/ι axioms — `refl_eq`
  takes no level arg, `ht_refl_eq (g)(v: lvl)` binds it), so a poly inductive
  (`Prod.{u,u}`, or a `structure Box.{u}`) at a generic level is just registered ONCE,
  level-generically (`register_inductive` with `inst = identity`, keeping its own params
  → `lv_u`, which `induct.generate` auto-detects and binds) and used by **plain const
  names — no level-application node at all**.  A shared `_ind_tag(levels)` returns `g`
  for a generic registration, the numeral tag otherwise.  No trusted-base change.
- **Whole-ENVIRONMENT certification** (`envcert_worker.py` / `envcert_sweep.py` /
  `envcert_demo.py`).  The strongest form of the thesis: not "do this file's `Eq`
  *obligations* certify?" but "does the 815-line stock base re-typecheck **every
  declaration** the kernel elaborated?"  For each decl with a body, certify `ht cnil
  <value> <type>` — the kernel's *own* typing, re-derived as an explicit stock-MM0
  proof, checked by **both** mm0-rs and mm0-c, faithful by construction (term and type
  are the kernel's).  This reaches **non-equational** propositions for free: `Nat.le`
  reflexivity/transitivity (induction over the indexed inductive), decidability via
  `Decidable.rec`, typeclass methods, plain data.  Remarkably it needed **zero**
  bridge/db_cert/trusted-base changes — purely a new harness over the existing
  `prove_ht`; everything the universe-polymorphism / opaque-lemma / `DefRef` work built
  is exactly what makes an arbitrary declaration typeable.  Run `envcert_sweep.py` for
  live numbers; at writing, **all 325 of 325** declarations across the 40 elaborated
  files re-typecheck end-to-end (every file fully), both-checkers invariant holding.
  (Enablers: generated **List/Vec are now universe-polymorphic** — element + container
  at a level variable `v` matching the kernel's `List.{u} (α : Sort u) : Sort u`, so
  poly `map`/`length`/`append`/`Vec_length` no longer demand `leveq u 1`; and
  **source-level axioms** — see next.)
- **Source-level axioms — certify *modulo* the source's axioms** (`axiom_demo.py`).  A
  proof resting on a Lean `axiom` (no body — `propext`, `Classical.choice`, `Quot.sound`,
  or a file's own) is certified by **carrying** the axiom as an explicit assumption: a
  `term <san>: expr;` + an mm0 `axiom ht_<san> (g)(lv..): ht g <san> <type>` (the
  asserted typing), atomic (shift/subst-invariant), level-agnostic in the term (a use at
  `.{1,0}` or generic `.{u,0}` resolves to the same const, MM0 unifying the levels).
  This is the honest treatment — contrast the opaque-lemma path, which *proves* a
  `theorem`'s typing because it has a body; an axiom has none, so we *assert* it, exactly
  as the Lean source — and Lean's own kernel — trust it.  The cert is valid *modulo the
  source's declared axioms*, which is what a proof checker should do, and
  `envcert_worker` reports them (`axioms=…`, the stock-MM0 `#print axioms`).  **db.mm1 —
  the CIC trusted base — is unchanged**: a source axiom is the *user development's*
  assumption, never a new CIC inference rule.  This closed the last envcert skips, so the
  whole environment saturates at 325/325.  (`bridge.register_axiom`,
  `db_cert.AXIOMS`/`gen_axiom_block`; all three workers emit the axiom block.)

**Direction (2026-06): this is becoming the production verifier.**  `src/mm0_verify.py`
(the Python verifier with its baked-in βιζ evaluator) is now **legacy** — the project is
moving to use **stock MM0 entirely**.  So the stock-MM0 certifier is no longer a parallel
proof-of-concept; promoting it to the real pipeline (and retiring `mm0_verify.py` + the
`lean.mm0` emitter path) is the **sanctioned destination**.

**Where it stands.**  Both whole-suite measures are now **saturated**: the `Eq`-obligation
sweep at 149/149 (every `Eq` goal by de-refl conversion or whole-proof typing), and
whole-environment certification at **325/325** — *every* declaration the kernel
elaborates across the 40 standalone-elaborating files is re-typechecked end-to-end by the
815-line stock base, both checkers, with assumed source axioms carried + reported.  **The
CIC trusted base (db.mm1) is unchanged throughout.**

**Remaining toward the swap:** (1) a first-class `verify`-a-`.lean`-file entry point
(promote `envcert` out of `experiments/`); (2) wire it into `run_all.py` / the test suite
in place of `mm0_verify.py`; (3) the ~19 files that don't elaborate under the standalone
`build_stdlib` need the fuller shared stdlib (a harness gap, not a certifier gap).  Other
*new* source shapes (orthogonal): mutual inductives; quotient types (`Quot`).  (Moving
βιζ + shift/subst1 out of the production trusted base is now down to that wiring.)

**Reproduce — and how the numbers are sourced.**  This section deliberately
states *capabilities, not counts*: figures (proof-node sizes, how many
obligations certify) shift as the bridge grows, so they live in script output,
not here.  From `experiments/stock_mm0_cert/` (build the checkers first; see the
experiment `README.md`):

- per-feature demos, each prints its own results + both checkers' verdicts:
  `run_db.py`, `run_db_typed.py`, `run_induct.py`, `bench.py`,
  `bridge_demo.py` (Nat), `bridge_list_demo.py`, `bridge_bool_demo.py`,
  `bridge_eq_demo.py`, `bridge_vec_demo.py`, `bridge_delta_demo.py` (δ),
  `bridge_poly_demo.py` (universe-poly), `bridge_struct_demo.py`
  (classes/structures — also surfaces the param-level gap on `arith.lean`),
  `freevar_demo.py` (free-variable de-refl obligations, e.g.
  `(m n : Nat) → add m (succ n) = succ (add m n)`),
  `levelgen_demo.py` (level-generic / open-universe obligations, e.g.
  `(α : Sort u) (x : α) → (fun z => z) x = x`, generic over `u`),
  `proofterm_demo.py` (whole proof TERMS that use the IH — `zero_add`, `add_comm`,
  `Bool.not_not`, level-poly `my_eq_symm.{u}`, … — typed via `ht cnil body type`),
  `opaque_demo.py` (modular proofs: a cited `theorem` lemma typed ONCE, used by
  reference — `add 0 n = n` cited twice stays small),
  `poly_opaque_demo.py` (a universe-poly `theorem` cited at a CONCRETE level
  `my_eq_symm.{1}`, monomorphised + typed once by reference),
  `poly_opaque_gen_demo.py` (a universe-poly `theorem` cited at a GENERIC level —
  `symm_symm.{u}` citing `my_eq_symm.{u}` — typed once, level-generically, by reference),
  `poly_def_gen_demo.py` (a universe-poly `def` at a GENERIC level — `mysym.{u}` via a
  `DefRef` that δ-unfolds), `poly_ind_gen_demo.py` (a universe-poly *inductive* at a
  GENERIC level — `structure Box.{u}`, registered level-generically),
  `envcert_demo.py` (whole-environment cert: NON-equational decls — `Nat.le`
  reflexivity/transitivity over the indexed inductive, `choose` via `Decidable.rec`),
  `axiom_demo.py` (certify a proof *modulo* a source `axiom`, carried + reported),
  `run_levels.py`, `capstone_demo.py`.
- whole-suite coverage: `python3 coverage_sweep.py` — runs `coverage_worker.py`
  over every `examples/*.lean` (subprocess per file, detector = `Eq A` over any
  type), certifying each obligation by **de-refl conversion** (rfl leaves) **or
  whole-proof typing** (`ht cnil body type` — induction / case analysis), prints a
  fresh per-file table + a **"Top skip reasons"** ranking (currently empty — the sweep
  is **saturated**), and **asserts** the invariant that every file with a certified
  obligation passes both mm0-rs and mm0-c (exits non-zero otherwise).  `coverage.md`
  describes the method; run the sweep for the current spread.
- whole-ENVIRONMENT coverage: `python3 envcert_sweep.py` — the stronger sibling: runs
  `envcert_worker.py` over every `examples/*.lean` and reports how many of *all*
  elaborated declarations (not just `Eq` goals) the stock base re-typechecks by typing
  `ht cnil value type`.  Same per-file table + invariant; names its own next target
  (`unsup:Eq.substI` — the user-axiom frontier above).
