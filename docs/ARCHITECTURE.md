# lean-mm0: A Metamath-Zero Backend for Lean

## Goal

Translate a Lean-like dependent type theory into Metamath Zero (MM0), so
that every Lean proof becomes an MM0 proof checkable by a tiny verifier.
The **trusted base** shrinks from "Lean's kernel + elaborator" to
"MM0 verifier + CIC axiomatisation in the MM0 prelude".

## Pipeline

```
   .lean.py source                  Lean kernel-AST + decls
        │                                   │
        ▼                                   ▼
   surface parser ─────────────────► kernel.elaborate
                                            │
                                  type-checks, records a derivation
                                            │
                                            ▼
                                   emitter.to_mm0(decl)
                                            │
                                            ▼
                                  .mm0 / .mmp text files
                                            │
                                            ▼
                                   mm0_verify.check(file)
                                            │
                                            ▼
                                       ✓  /  ✗
```

## Layering & trust

| Layer | LOC budget | Trusted? |
|-------|-----------|----------|
| MM0 verifier (`mm0_verify.py`) | < 600 | YES — the only trusted code |
| `prelude/cic.mm0` (axioms of CIC) | < 400 | YES — the trusted theory |
| Lean kernel (`kernel.py`) | ~1500 | no (its outputs are re-checked) |
| Emitter (`emitter.py`) | ~600 | no |
| Surface / inductive compiler | unbounded | no |

If a buggy elaborator produces a wrong Lean term and a wrong "proof",
the MM0 verifier will reject the resulting `.mmp` — that is exactly the
guarantee MM0 buys us.

## Encoding of CIC in MM0

MM0 is essentially first-order with sort declarations, term constructors,
definitions, axioms, and forward-only proofs. To embed CIC we declare:

```
sort lvl;            -- universe levels
sort expr;           -- CIC terms (deeply embedded)
sort ctx;            -- typing contexts (lists of expr)
```

with term constructors mirroring the AST:

```
term lzero:  lvl;
term lsucc:  lvl > lvl;
term lmax:   lvl > lvl > lvl;
term limax:  lvl > lvl > lvl;

term esort:  lvl > expr;
term evar:   nat > expr;
term eapp:   expr > expr > expr;
term elam:   expr > expr > expr;        -- (dom, body)  body uses (evar 0)
term epi:    expr > expr > expr;
term elet:   expr > expr > expr > expr; -- (type, value, body)
term econst: name > lvls > expr;        -- name applied to level args
```

A *typing judgement* and a *definitional-equality judgement* are
introduced as propositions:

```
term ht: ctx > expr > expr > wff;       -- Γ ⊢ t : T
term de: ctx > expr > expr > wff;       -- Γ ⊢ s ≡ t
```

Then we axiomatize the CIC inference rules:

```
axiom ht_var:    ht (cons T G) (evar 0) (lift1 T)
axiom ht_weak:   ht G t T  →  ht (cons S G) (lift1 t) (lift1 T)
axiom ht_sort:   ht G (esort l) (esort (lsucc l))
axiom ht_pi:     ht G A (esort u)
              →  ht (cons A G) B (esort v)
              →  ht G (epi A B) (esort (limax u v))
axiom ht_lam:    ht G A (esort u)
              →  ht (cons A G) b B
              →  ht G (elam A b) (epi A B)
axiom ht_app:    ht G f (epi A B)
              →  ht G a A
              →  ht G (eapp f a) (subst1 a B)
axiom ht_conv:   ht G t T  →  de G T T'  →  ht G T' (esort u)
              →  ht G t T'
... (β, δ, ζ, ι, η, level-substitution, ...)
```

For each `inductive` declaration we add *family-specific* axioms:
the type former, constructors, and ι-rule for the recursor.  These are
generated mechanically from the inductive's signature.

## Proof scripts

MM0 proof scripts (`.mmp`) are forward-only sequences:

```
theorem add_comm: ht G' add_comm_body add_comm_type :=
  (ht_app (ht_app (ht_const "Nat.rec" [...]) ...) ...);
```

The emitter records, during kernel type-checking, which axiom/theorem
was invoked at each step and emits the corresponding term tree.

## Status legend in tests

Each test in `tests/` carries a status comment:

* `# status: pass` — kernel accepts, MM0 emits, MM0 verifies
* `# status: kernel-only` — kernel accepts but emitter cannot lower yet
* `# status: skip` — out of scope for the prototype

The CI script reports coverage by feature category.
