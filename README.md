# lean-mm0

A prototype **Metamath Zero** backend for **Lean** — translate a small
Lean-like dependent type theory into MM0 proofs that a tiny, auditable
verifier can re-check independently of Lean itself.

## Status snapshot

| | |
|---|---|
| Tests passing | **65 / 65** (across 4 test files) |
| Test categories | propositional, equality, naturals, polymorphic, predicate logic, inductives, let/ζ, higher-order, recursors, instantiation, computation, indexed inductives, indexed Prop, quotients, parsed-source |
| Trusted base | `src/mm0_verify.py` (~480 LOC) + `prelude/cic.mm0` (~165 LOC) |
| Untrusted | kernel + emitter + inductive compiler + parser (~3.5 kLOC) |
| Pipeline | `.lean` text → kernel AST → kernel checks → MM0 emit → MM0 verify |

## What works

* Full **CIC** with βιδζ at the verifier level (so `Nat.add 2 3 = 5` is provable by `Eq.refl`)
* Universe-polymorphic Pi / Lam / Let / Sort, max / imax level algebra
* **Non-indexed inductives** with auto-generated recursor and ι rules:
  `Bool, Nat, List.{u}, And, Or, True, False, Prod.{u,v}, Sum.{u,v}, Option.{u}, Sigma.{u,v}`
* **Indexed inductive families** with index templates:
  `Eq.{u}`, `Vec.{u}` (with `Vec.length` definable by `Vec.rec` and
  `length [7,8] = 2` checkable by `Eq.refl`),
  `Nat.le` (indexed Prop, recursive constructor with index template)
* **Quotient types** as kernel primitives:
  `Quot.{u}, Quot.mk, Quot.lift, Quot.ind, Quot.sound`
  with the `Quot.lift f h (Quot.mk r a) = f a` ι-rule
* **Recursor eliminators**: `Nat.pred, Bool.not, Bool.and, Eq.subst, Eq.symm`
* **Tiny Lean-4 surface parser** (`src/lean_parser.py`):
  fully explicit `def / axiom / theorem` with explicit binders, lambdas,
  Pi types, let-bindings, universe instantiation `.{u, v}`, and numeric
  `Nat` literals.  `examples/demo.lean` is parsed, kernel-checked, MM0-emitted
  and MM0-verified end to end.

## What's *not* supported

Compared to real Lean / mathlib, the prototype is missing — in
rough order of difficulty:

| Feature | Why it's hard |
|---|---|
| Implicit arguments + unification | Needs a real elaborator |
| Type-class resolution | Needs an instance-synth solver |
| Tactic language | Needs macro / monadic state / proof terms generation |
| Notation & macros | Needs the Lean syntax engine |
| Mutual / nested inductives | Needs the "encoding-as-single-inductive" pass |
| Proof irrelevance (definitional Prop equality) | Verifier doesn't carry types |
| Pattern matching / `match` | Compiles to recursors but needs a coverage checker |
| Decidable equality / DecidableEq derivation | Needs simp/term unification |
| Structures, projections, `mkApp` machinery | Easy to add for plain records |
| The actual mathlib source | ~1.4 M LOC of Lean depending on the above |

## A blunt scope statement

Translating *all of mathlib* through a one-person, one-session prototype
is not realistic.  Mario Carneiro's production `lean2mm0` has been
worked on for years and still does not cover all of mathlib; the
gap is dominated by elaboration, tactics, and the Lean macro system —
not the kernel.  This prototype focuses on the **kernel-and-below**
layer: it shows that the *pipeline architecture* (Lean source →
recorded derivations → MM0 proofs → tiny verifier) is sound and works
end-to-end.  Extending it upward toward the elaborator is a research
project.

## Pipeline

```
   .lean source                     MM0 axiomatisation
   (examples/*.lean)                (prelude/cic.mm0)
        │                                    │
        ▼                                    │
   lean_parser.elaborate ──► kernel AST + decls
                                      │
                                      ▼
                            kernel.add_definition
                            (records derivation tree)
                                      │
                                      ▼
                            emitter.emit_env(...)
                                      │
                                      ▼
                            MM0 source text  ◄────────┘
                                      │
                                      ▼
                            mm0_verify.verify_text
                                      │
                                      ▼
                                  ✓  /  ✗
```

## Trust boundary

| Component | Lines | Trusted? |
|-----------|-------|----------|
| `src/mm0_verify.py` (MM0 verifier) | ~480 | **YES** |
| `prelude/cic.mm0` (CIC axiomatisation) | ~165 | **YES** |
| `src/kernel.py` | ~470 | no |
| `src/inductive.py` | ~210 | no |
| `src/emitter.py` | ~510 | no |
| `src/lean_parser.py` | ~330 | no |

A bug in any "no" component can only produce MM0 the verifier rejects.

## Running the tests

```bash
$ python run_all.py
```

Runs:

1. `tests/test_kernel_smoke.py` — kernel unit tests
2. `tests/test_emit_basic.py` — emit + verify the stdlib
3. `tests/suite.py` — categorised end-to-end suite
4. `tests/test_parser.py` — parse `examples/demo.lean`, then emit & verify

## Layout

```
lean-mm0/
├── src/
│   ├── levels.py            universe-level algebra
│   ├── expr.py              CIC expression AST, de Bruijn
│   ├── env.py               declaration store
│   ├── kernel.py            type checker + derivation recorder
│   ├── inductive.py         compiles non-indexed inductives
│   ├── prelude_decls.py     hand-built stdlib + indexed + quotients
│   ├── lean_parser.py       tiny Lean-4 subset parser
│   ├── emitter.py           Lean derivation → MM0 proof text
│   └── mm0_verify.py        ← TRUSTED ← s-expression MM0 verifier
├── prelude/
│   └── cic.mm0              ← TRUSTED ← CIC axioms in MM0 syntax
├── examples/
│   └── demo.lean            consumable by the parser
├── tests/
│   ├── test_kernel_smoke.py
│   ├── test_emit_basic.py
│   ├── suite.py             49 categorised end-to-end tests
│   └── test_parser.py
├── docs/
│   └── ARCHITECTURE.md
├── run_all.py
└── README.md
```
