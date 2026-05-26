# lean-mm0 — Handoff

This is a working prototype Metamath-Zero backend for a Lean-flavoured
dependent type theory.  The goal: shrink the trusted base of a Lean-style
proof down to a tiny verifier — about 670 lines of trusted code (the
MM0 verifier plus a CIC axiomatisation in MM0 syntax) — while everything
else (kernel, elaborator, emitter, parser, ~6.6 kLoC) lives outside the
trust boundary.

## Current state

| | |
|---|---|
| Tests | **112 passing** across 4 files (7 kernel smoke + 3 emit basic + 57-test suite + 45 parser examples) |
| Total source | ~6.8 kLoC Python + 188 LoC MM0 prelude + ~2450 LoC `.lean` examples (45 files) |
| Trusted base | `src/mm0_verify.py` (710 LoC) + `prelude/cic.mm0` (188 LoC) |
| Repo | 55+ commits on `master`; clean working tree |

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
│   └── mm0_verify.py   ← TRUSTED: MM0 s-expression verifier (669 LoC)
├── examples/           37 .lean files (1337 LoC) that compile + verify
├── tests/
│   ├── test_kernel_smoke.py   (7 tests)
│   ├── test_emit_basic.py     (3 tests)
│   ├── suite.py               (57 tests across 14 categories)
│   └── test_parser.py         (37 .lean examples, each round-tripped)
└── run_all.py          single entry point: runs all 4 test files
```

To run everything:

```bash
$ cd lean-mm0
$ python run_all.py
```

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
| `infix / infixl / infixr [:prec] OP NAME` | binary infix operators with precedence | arith.lean |

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
| `rewrite h` / `rw h` | h : Eq α a b — replaces all syntactic occurrences of `a` in the goal with `b`; leaves the rewritten goal as a subgoal |
| `cases h` | h : `Ind params indices` — emits a recursor app with one fresh meta per ctor as a subgoal.  Each subgoal has type `Π fields, Π ihs, goal`; user `intro`s the fields and IHs.  Non-dependent motive (goal stays G in every branch).  Indexed inductives are supported; the motive is constant over indices too — so case-splits on a proof of `Nat.le n m`-style hypothesis succeed but each branch sees the abstract original G, no index-specialisation |
| `induction h` | Like `cases h` but with a **dependent** motive — each subgoal's goal is `G[h := ctor pattern]` (specialised, not the abstract original) and each IH has type `motive(rec_field)`.  Requires `h` to be a local FVar.  For *indexed* inductives, also requires every index in `h`'s type to be an FVar (so we can abstract it into the motive's binders); concrete indices would need index unification, not done.  Other context hypotheses depending on an abstracted index keep their original types (no auto-revert).  Subgoal-local intros chained with another `apply` and an `exact <fvar>` close correctly (the wrap is deferred until after all subgoals are solved) |
| `t1; t2; ...` | seq — focused-goal semantics: each tactic acts on the current focused goal.  Main intros are deferred until the very end so subgoal solutions can reference them as FVars; subgoal-local intros are wrapped into Lams immediately |
| `revert h` | inverse of `intro`: pulls a hypothesis intro'd earlier in the same `by` block back into the goal as a leading Π binder.  Pops the entry from ctx, closes the goal over its FVar, wraps with Π.  Refuses if a later intro depends on `h` (revert that one first).  Only works on intros, not on theorem binders |

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

48 commits — feature commits + HANDOFF updates interleaved:

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
(next)   List theorems: length_map, map_append, map_compose
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
| `Decidable` / `if then else` | implemented (`Decidable.isTrue/isFalse`, `ite`, `if/then/else` sugar, `Nat.decEq`, `Bool.decEq`, composition `And`/`Or`/`Not`) | — |
| `rewrite` / `rw` tactic | implemented (builds `Eq.rec` with motive abstracting LHS) | — |
| `cases` tactic | implemented (v1+v2: non-recursive and recursive ctors; non-dependent motive only — see below) | dependent motive would need each minor's return type to be `G[scrut := ctor_pattern]` with careful BVar bookkeeping |
| `apply` tactic (with subgoal generation) | implemented; subgoals carry ctx snapshots and survive intro/seq context switches | — |
| `simp` tactic | not implemented | needs an equation database + fixpoint iteration |
| `induction` tactic | implemented (`examples/induction.lean`, `examples/indexed_cases.lean`): dependent motive, IH typed at the recursive sub-term.  Works for Nat, Bool, List, **and indexed inductives like Nat.le when their indices in the scrutinee's type are FVars**.  Subgoal-local intros chained through further `apply`s + `exact <fvar>` work too (wrap deferred to end-of-seq).  Auto-revert of dependent hypotheses + index unification (for concrete indices) not done |
| `revert` tactic | implemented (`examples/revert.lean`) — `revert h` pulls an intro back into the goal as a leading Π.  Naturally pairs with `induction` to generalise a hypothesis before inducting on another |
| Full `match` syntax in `def` (`def f \| 0 => 0 \| succ k => k`) | not implemented | needs equation compiler |
| Match on indexed inductives with recursive ctors (`Vec.cons`, `Nat.le.step`) | not implemented | needs IH-motive-application logic that threads per-rec-arg index expressions |
| Mutual inductives w/ cross-recursor | partial (constructors only) | needs the "tag-encoding" pass |
| Notation/macro system | minimal (only `infix*`) | real Lean macros are a programmable language |
| Proof irrelevance | axiom in prelude; not auto-applied | needs type-aware def-eq |
| Module/`import` system | not implemented | minimal value for a prototype |
| Mathlib itself | unreachable in any chat session | depends on ~all of the above plus 1M+ LoC of Lean |

For most of these, a small first version is tractable; see "where to pick
up" below.

## Where to pick up

Pieces ordered by impact and tractability:

1. **More Nat algebra / ordering** — `add_zero`, `mul_zero`, `mul_one`,
   `add_assoc`, `zero_mul`, `one_mul` (`nat_lemmas.lean`); `succ_mul`,
   `mul_comm`, `left_distrib`, `mul_assoc`, `right_distrib`,
   `add_left_comm` (`nat_mul.lean`); `le_refl`, `le_trans`
   (`nat_le.lean`); `le_succ`, `le_succ_of_le`, `zero_le`,
   `succ_le_succ`, `lt_succ_self`, `lt_succ_of_lt`, `le_of_lt`
   (`nat_le_more.lean`) are done.  Open: `le_antisymm`, `lt_irrefl`,
   `le_total` (these last few want indexed-inductive case analysis,
   which is the next engine fix — see item 4).

2. **More tactics** — `rewrite` (`5380a78`), `cases` v1+v2 (`282e66d`,
   `bcfcd73`), `induction`, and `revert` are in.  Next: `simp`
   (rewrite using an equation database), index unification + auto-revert
   for `induction` on indexed inductives with concrete indices.

3. **More Decidable instances** — `And` / `Or` / `Not` (`decidable_compose.lean`),
   `Nat.decEq` (`nat_dec_eq.lean`), `Bool.decEq` (`bool_dec_eq.lean`),
   `List.decEq` for `List Nat` (`list_dec_eq.lean`), and a polymorphic
   `List.decEq` (`list_dec_eq_poly.lean`) parameterised over an
   element-wise decidable equality are done.  Open: `Decidable (Nat.le a b)`,
   `Decidable (Nat.lt a b)`, decidable membership for lists.

4. **Indexed-inductive match v2 (recursive ctors)** — extend the v1
   indexed match to handle `Nat.le.step`, `Vec.cons`, etc.  Needs the
   IH-motive-application logic to thread per-rec-arg index expressions.

5. **Notation/macro system** — Generalise `infix` to arbitrary mixfix
   notation like `notation:50 "[" a "," b "]" => Prod.mk a b`.
   Needs a more flexible token-pattern parser.

6. **Mutual inductives' cross-recursor** — Compile mutual `inductive`
   blocks to a single tag-discriminated inductive, generate a
   cross-recursor.  Substantial.

7. **Lean elaborator-compat layer** — Read actual `.lean` files from
   Lean 4 source by being more permissive about syntax (newlines as
   separators, more notation forms).  Real Lean files require
   elaborator features that aren't trivially in scope, but a useful
   subset is reachable.

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
