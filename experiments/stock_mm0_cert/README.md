# Prototype: a certifying emitter (CIC → stock MM0)

**Status:** working proof-of-concept for **substitution, β, and ι
(recursors)** — all generating stock-MM0 certificates that `mm0-rs` *and*
`mm0-c` verify.  Fully-concrete ground numerals (`1+1=2`) are blocked by an
α-renaming wall in the *named-binder* `lean.mm1` prelude (see Findings) —
the fix is a **de-Bruijn** prelude matching our own verifier.

## Why

Today our trusted base is `src/mm0_verify.py`, which **computes** βδιζ
inside the trusted core (its `_normalize`).  That is a real, load-bearing
extension over stock Metamath Zero, which has *no* computation — its
verifier only does first-order substitution + matching + proof-driven
`def` unfold (confirmed by reading `mm0-c/verifier.c`).

Experiment #1 (see HANDOFF) established:
- stock MM0 *can* express CIC: `mm0/examples/lean.mm1` (Mario Carneiro) is
  a full CIC axiomatisation that `mm0-rs` and `mm0-c` verify in ~18 ms;
- but every reduction must be an **explicit proof**, and hand-authoring it
  drowns in MM0's named-binder / disjoint-variable bookkeeping (I hit
  α-violations three times writing a 2-step computation by hand).

This prototype tests the obvious response: **let an untrusted emitter
generate those proofs.**  If it can, we can drop the βδιζ evaluator from
the trusted base and check our output with a stock, multiply-reimplemented,
soon-formally-verified kernel.

## What it does

`cert.py` (Layer 1) and `cert_beta.py` (Layer 2) take CIC terms (in
`lean.mm1`'s named syntax) and emit **explicit stock-MM0 proofs** of
conversions our verifier discharges with a single `de-refl`.

- **Layer 1 — substitution.** `prove_subst(A,e,x)` emits a proof of
  `subst: A[e/x] = B` from `subst_var / subst_nf / subst_app /
  subst_lambda / subst_Pi`.  Self-contained (these axioms need no typing).
- **Layer 2 — β.** `prove_type` (a typing certifier for the λ-fragment +
  nat constants) and `prove_whnf` (leftmost-outermost weak-head reduction)
  emit `conv_beta` + the Layer-1 substitution proofs + app-congruence
  (`conv_ty_ndapp`), chained with `conv_trans`.

**The key idea:** a global **fresh-name supply** for binders.  Every binder
is unique, so substitution and congruence never hit a variable capture —
the α/DV bookkeeping that made hand-authoring impractical is *automatic*.

## Results (checked by mm0-rs AND mm0-c)

| certificate | explicit nodes | ours |
|---|---|---|
| `(f x)[a/x]` | 3 | 1 `de-refl` |
| iota-typing subst `(C n → C (succ n))[zero/n]` | 9 | 1 |
| 25-deep spine `f²⁵ x [a/x]` | 51 | 1 |
| β: `(λx. x) a = a` | 3 | 1 |
| β: K `(λp.λq. p) a b = a` | 20 | 1 |
| β: K3 `(λp.λq.λr. p) a b c = a` | 44 | 1 |
| β: nested `(λx. (λy. y) x) a = a` (chains 2 β) | 12 | 1 |
| ι: `rec u C z s (succ¹ 0)` (abstract C,z,s) | 14 | 1 |
| ι: `rec u C z s (succ² 0)` | 41 | 1 |
| ι: `rec u C z s (succ³ 0)` | 83 | 1 |

The generated K-combinator proof is byte-for-byte the one hand-authored in
experiment #1 — but produced instantly, no α-fighting.  The ι certificates
are the generated, arbitrary-depth version of experiment #1's hand-written
`ground_two_steps`.  Certificate size grows linearly per reduction step
(~27 nodes / recursor step); checking is trivially fast.

## Run

Requires the sibling `mm0` clone built (`mm0-rs` + `mm0-c`):
```
mm0-rs:  cd ../../../mm0 && cargo build --release   # in mm0-rs/
mm0-c:   cd ../../../mm0/mm0-c && gcc main.c -O2 -D NO_PARSER -o mm0-c-np
```
Then:
```
python3 run_layer1.py      # substitution certificates
python3 run_layer2.py      # beta certificates
python3 run_iota.py        # recursor (iota) certificates
```
Each prints the generated `.mm1`, a node-count table, and the verdict from
both checkers.  Generated fragments land in `_gen_layer{1,2}.mm1`.

## Finding: the α wall (why concrete numerals need a de-Bruijn prelude)

ι with **abstract** motive/z/s works (above).  But a **concrete** ground
computation (e.g. `1+1=2`) feeds a concrete successor `s = λk.λih. succ ih`
to the iota lemma, and there it dies — exactly where experiment #1 died by
hand.  The mechanism, now confirmed empirically:

- `nat_succ_iota` carries a disjoint-variable condition `n ∉ s` (its bound
  `n` must not occur in the term substituted for `s`).
- A concrete `s` is a λ, so it *binds* some variable.  `ty_lambda` rigidly
  ties the Pi **type**-binder to the λ **term**-binder, and mm0 will **not**
  α-rename it (tested: `variables do not match: nq != w`).
- So matching the lemma's h3 type (binder `n`) forces `s`'s binder to be
  `n` — but then `n ∈ s`, violating the DV condition.  Contradiction.

This is a property of `lean.mm1`'s **named-binder** representation, not of
the approach.  **Our own verifier uses de Bruijn indices — no binder names,
no α — which is precisely why it sidesteps this.**  So the concrete path is:

## Roadmap

1. **De-Bruijn stock-MM0 prelude.**  Re-encode CIC with de Bruijn indices
   (like our `prelude/cic.mm0`), but with `shift` / `subst1` as *axiomatised
   provable relations* (per-constructor axioms) instead of trusted builtins.
   This eliminates α entirely and moves `shift`/`subst1` out of the trusted
   base.  The emitter already thinks in de-Bruijn-ish terms, so this is the
   natural target and unblocks concrete numerals (`four_eq`).
2. **δ.**  Wire in MM0 statement-level `def` unfolding (the one reduction
   stock MM0 does natively).
3. **Kernel integration.**  Read our `src/expr.py` CIC AST instead of the
   hand-built terms here, i.e. replace `src/emitter.py`'s `de-refl`
   shortcut with generated conversion certificates.

The β/ι/subst generators here carry over directly; only the prelude's
binder representation changes.

## Files
- `cert.py` — term AST (incl. `Imp`, `NatRec`), pretty-printer, Layer-1
  substitution certifier.
- `cert_beta.py` — Layer-2 typing certifier + whnf β-reducer.
- `cert_iota.py` — Layer-3 recursor reducer (`norm_rec`).
- `run_layer1.py`, `run_layer2.py`, `run_iota.py` — drivers (generate + check).
- `_gen_layer1.mm1`, `_gen_layer2.mm1`, `_gen_iota.mm1` — last generated output.
