# Prototype: a certifying emitter (CIC → stock MM0)

**Status:** working proof-of-concept generating stock-MM0 certificates that
`mm0-rs` *and* `mm0-c` verify, for substitution, β, ι (recursors), and —
via a **de-Bruijn prelude** (`db.mm1`) — **fully-concrete ground numerals
including `1+1=2`**, with `shift`/`subst1` *proven* (out of the trusted
base) rather than computed.

Two tracks:
- **`lean.mm1` (named binders):** Layers 1–3 (`cert*.py`) — subst, β, ι with
  abstract algebra.  Hits an α-wall on concrete numerals (see Findings).
- **`db.mm1` (de Bruijn):** the wall-free track (`db_cert.py`) — reaches
  concrete ground computations end-to-end.  **This is the real path.**

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

### De-Bruijn track (`db.mm1`) — concrete ground computations

These reach a *real* numeral result — what the named track could not — with
`shift`/`subst1` proven, not built in (`run_db.py`):

| computation | normal form | nodes | ours |
|---|---|---|---|
| `rec (λ_.N) 0 (λk ih. S ih) (S 0)` | `1` | 37 | 1 |
| same on `S S 0` | `2` | 75 | 1 |
| **`add 1 1`** (2 outer β + ι + inner β) | **`2`** | 92 | 1 |
| `add 2 1` | `3` | 98 | 1 |

`add = λm.λn. rec (λ_.N) m (λk.λih. S ih) n`.  Verified by mm0-rs and the
minimal mm0-c kernel.  No α anywhere (de Bruijn has no binder names), so the
emitter needs no fresh-naming tricks — the wall simply doesn't exist.

## Run

Requires the sibling `mm0` clone built (`mm0-rs` + `mm0-c`):
```
mm0-rs:  cd ../../../mm0 && cargo build --release   # in mm0-rs/
mm0-c:   cd ../../../mm0/mm0-c && gcc main.c -O2 -D NO_PARSER -o mm0-c-np
```
Then:
```
python3 run_layer1.py      # substitution certificates   (lean.mm1 track)
python3 run_layer2.py      # beta certificates           (lean.mm1 track)
python3 run_iota.py        # recursor (iota), abstract   (lean.mm1 track)
python3 run_db.py          # concrete numerals, 1+1=2    (de-Bruijn track)
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

1. ✅ **De-Bruijn stock-MM0 prelude** (`db.mm1`) with `shift`/`subst1` as
   provable relations — DONE; reaches `1+1=2` (above).
2. **Full CIC in the de-Bruijn prelude.**  `db.mm1` is deliberately small:
   untyped `deq`, Nat hard-wired as opaque constants, ι stated as untyped
   axioms.  To be a real *trusted base* it needs the typing judgment
   (`has_type` + the CIC rules, as in `prelude/cic.mm0`) and ι gated on
   typing (or the general inductive machinery).  The reduction certificates
   here carry over unchanged; this adds the typing layer around them.
3. **δ.**  MM0 statement-level `def` unfolding (the one reduction stock MM0
   does natively) for our `def`s.
4. **Kernel integration.**  Drive the emitter from our `src/expr.py` CIC AST
   (it already maps onto these de-Bruijn terms), replacing `src/emitter.py`'s
   `de-refl` shortcut with generated conversion certificates — at which point
   the verifier's βιζ + shift/subst1 evaluator can leave the trusted base.

## Files

**`lean.mm1` (named-binder) track:**
- `cert.py` — term AST (incl. `Imp`, `NatRec`), pretty-printer, Layer-1
  substitution certifier.
- `cert_beta.py` — Layer-2 typing certifier + whnf β-reducer.
- `cert_iota.py` — Layer-3 recursor reducer (`norm_rec`).
- `run_layer1.py`, `run_layer2.py`, `run_iota.py` — drivers.

**`db.mm1` (de-Bruijn) track — the real path:**
- `db.mm1` — de-Bruijn stock-MM0 prelude; `shift`/`subst1` as provable
  relations, untyped `deq`.  Pure axioms (the trusted spec).
- `db_cert.py` — certifying evaluator: `prove_shf` / `prove_sub` /
  `prove_norm` (β + ι, full normalisation).
- `run_db.py` — driver: concrete ground computations incl. `1+1=2`.

Generated output (`_gen_*.mm1`) is gitignored.
