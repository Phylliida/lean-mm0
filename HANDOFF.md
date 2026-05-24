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
| Tests | **89 passing** across 4 files (7 kernel smoke + 3 emit basic + 57-test suite + 22 parser examples) |
| Total source | ~6.0 kLoC Python + 188 LoC MM0 prelude + 740 LoC `.lean` examples |
| Trusted base | `src/mm0_verify.py` (669 LoC) + `prelude/cic.mm0` (188 LoC) |
| Repo | 7 commits on `master`; clean working tree |

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
├── examples/           21 .lean files (708 LoC) that compile + verify
├── tests/
│   ├── test_kernel_smoke.py   (7 tests)
│   ├── test_emit_basic.py     (3 tests)
│   ├── suite.py               (57 tests across 14 categories)
│   └── test_parser.py         (21 .lean examples, each round-tripped)
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
| `theorem` (same shape, treated identically) | `theorem foo : T := proof` | math.lean |
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
| `match`/case | `match e : T with \| ... \| ...` (Nat, Bool, polymorphic List) |
| Recursive `def` via top-level `match` | structural recursion → recursor IH (Nat, List) |
| Numeric literals | `3` → `Nat.succ (Nat.succ (Nat.succ Nat.zero))` |
| `by TAC` proofs | `by rfl`, `by intro x; exact x` |

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
| `intro x` | if goal is `Π x : T, U`, push `x` to ctx and run the rest of the block with the body as the new goal |
| `apply f` | elaborate `f`, peel its Π binders as fresh metas, unify the return type with the goal; explicit metas the unifier didn't pin become subgoals |
| `assumption` | succeed if some local hypothesis (innermost-first) is def-equal to the goal |
| `t1; t2; ...` | sequence — `apply` deposits subgoals into a queue, subsequent tactics drain them in order |

## Trust boundary detail

**Trusted (~857 LoC total):**

1. `src/mm0_verify.py` (669 LoC).  Parses an s-expression dialect of MM0
   (sorts, term ctors, defs, builtins, axioms, theorems, iota rules).
   Verifies forward proofs by substituting the proof's term arguments
   into an axiom/theorem's hypotheses + conclusion, normalising the
   result (βδιζ + level laws + a few builtins like `subst1`/`shift`),
   and comparing.  Iota rules drive recursor reduction.

2. `prelude/cic.mm0` (188 LoC).  Declares the syntactic categories
   (`expr`, `lvl`, `ctx`, `name`) and the inference rules of CIC as
   MM0 axioms: `ht-sort`, `ht-pi`, `ht-lam`, `ht-app`, `ht-conv`,
   `ht-let`, `de-beta`, `de-refl`, etc.

**Untrusted (everything else).**  A bug here cannot make the verifier
accept something false — only reject something true.

## What's been built (chronological)

7 commits, each adding a coherent slice:

```
383b984  Initial commit: lean-mm0 prototype
1cce7c4  Add structure inheritance, Sub class, Nat.pred to stdlib
5c4e219  List operations + first non-trivial induction proof
d2c7c9a  Eq.symm, Eq.trans in stdlib; succ_add and add_comm proofs
be3e47f  Tiny tactic monad: by rfl/exact/intro
39daebb  Handoff doc
e579ba5  apply + assumption tactics; subgoal-aware seq
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
| `Decidable` / `if then else` | not implemented | requires Decidable typeclass + propagation through elaboration |
| `simp`, rewriting tactic | not implemented | needs the tactic monad to be more general |
| `apply` tactic (with subgoal generation) | basic version implemented | a full version would handle subgoals escaping `intro` and named goals |
| Full `match` syntax in `def` (`def f \| 0 => 0 \| succ k => k`) | not implemented | needs equation compiler |
| Mutual inductives w/ cross-recursor | partial (constructors only) | needs the "tag-encoding" pass |
| Notation/macro system | minimal (only `infix*`) | real Lean macros are a programmable language |
| Proof irrelevance | axiom in prelude; not auto-applied | needs type-aware def-eq |
| Module/`import` system | not implemented | minimal value for a prototype |
| Mathlib itself | unreachable in any chat session | depends on ~all of the above plus 1M+ LoC of Lean |

For most of these, a small first version is tractable; see "where to pick
up" below.

## Where to pick up

Pieces ordered by impact and tractability:

1. **`Decidable` + `if then else`** — Inductive type with two ctors
   plus elaboration of `if EXPR then ... else ...` to a
   `Decidable.casesOn` invocation.  Notation system probably needs to be
   richer than what's there.  ~200 LoC.

2. **`apply` subgoals escaping `intro`** — Currently the tactic monad
   refuses to let an unsolved subgoal cross an `intro` boundary (the
   `fv` would dangle).  The fix is to abstract the subgoal's type into
   a Π over the introduced binder and reassign the meta with a Lam.
   Unlocks `intro h; apply f h` style proofs where `f` produces a goal
   referencing `h`.

3. **Recursion-on-multiple-args / dependent match** — Currently match
   only handles non-dependent motives.  A small extension is to let the
   user supply a motive explicitly with `match e (motive := ...) with`.

4. **`Nat.mul_comm`, `Nat.add_assoc`, `Nat.mul_one`** — Each follows the
   `add_comm` pattern; would build out a real `Nat` namespace.  ~1 page
   each.  Pure source-side work, no engine changes.

5. **More tactics** — `rewrite` (instantiate `Eq.mpr` / `Eq.rec` with
   HOP motive), `simp` (rewrite using an equation database), `revert`
   (the inverse of `intro`, needed to make subgoals abstractable).

6. **Notation/macro system** — Generalise `infix` to arbitrary mixfix
   notation like `notation:50 "[" a "," b "]" => Prod.mk a b`.
   Needs a more flexible token-pattern parser.

7. **Mutual inductives' cross-recursor** — Compile mutual `inductive`
   blocks to a single tag-discriminated inductive, generate a
   cross-recursor.  Substantial.

8. **Lean elaborator-compat layer** — Read actual `.lean` files from
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

- The MM0 verifier's normalisation handles β, δ (via `def`), ζ, ι (via
  `iota` declarations), and level normalisation — all transitively.
  When debugging "verifier rejects", normalize the failed term to see
  what it actually reduces to.

## Caveat

This is a research prototype written in a series of chat sessions.  It's
not optimised; some constructions are intentionally simple where a
production system would be sophisticated (no caching, no incremental
elaboration, no proper diagnostic reporting).  But the kernel is real,
the trust boundary holds, and the examples genuinely verify end-to-end.
