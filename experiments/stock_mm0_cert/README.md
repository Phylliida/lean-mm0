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
  concrete ground computations end-to-end, and now carries the **core CIC
  typing judgment** so a *typed* theorem can route a reduction certificate
  through `ht_conv`.  **This is the real path.**

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
| `rec (λ_.N) 0 (λk ih. S ih) (S 0)` | `1` | 300 | 1 |
| same on `S S 0` | `2` | 473 | 1 |
| **`add 1 1`** (2 outer β + ι + inner β) | **`2`** | 361 | 1 |
| `add 2 1` | `3` | 373 | 1 |

`add = λm.λn. rec (λ_.N) m (λk.λih. S ih) n`.  Verified by mm0-rs and the
minimal mm0-c kernel.  No α anywhere (de Bruijn has no binder names), so the
emitter needs no fresh-naming tricks — the wall simply doesn't exist.  (Node
counts include the per-ι-step **typing proof** that gates each iota — see
below; before gating these were 37 / 75 / 92 / 98.)

### Typing layer (`db.mm1` + `run_db_typed.py`)

`db.mm1` now carries the core CIC typing judgment `ht G e T` (`ht_sort`,
`ht_var0`/`ht_weak`, `ht_pi`, `ht_lam`, `ht_app`, `ht_conv`) plus Nat as a
typed primitive (`ht_nat`/`ht_zero`/`ht_succ`) — mirroring `prelude/cic.mm0`.
This makes it a sound-core trusted base, not just a reduction relation.

`run_db_typed.py` generates a *typed* theorem (106 nodes, checked by both):
```
db_typed (cP : Nat -> Sort lu) (h : cP (add 1 1))  ⊢  h : cP 2
```
The conclusion holds ONLY because `add 1 1 ≡ 2`; `ht_conv` consumes the
reduction certificate as its `def_eq` premise.  So typing, conversion, and
the reduction engine compose end-to-end in stock MM0 — with βιζ + shift +
subst1 entirely outside the trusted core.

### Gated ι — closing the soundness gap

`trec` now has a real type (`ht_rec`: `trec : Π C, C 0 → (Π n, C n → C (S n))
→ Π m, C m`), and ι is **gated on the recursor being well-applied**:

```
deq_iota_zero : ht g (trec @ cC @ z @ s) mt  →  deq g (rec cC z s 0) z
deq_iota_succ : ht g (trec @ cC @ z @ s) mt  →  ht g k tnat  →
                deq g (rec cC z s (S k)) (s k (rec cC z s k))
```

`ht g (trec @ cC @ z @ s) mt` can hold *only* via `ht_rec` + `ht_app`, which
forces `cC`/`z`/`s` to typecheck at the recursor's signature (with the
motive-substitution done by the `sub` relation).  So ι is now a sound,
type-preserving definitional equality, not an untyped rewrite.  The emitter
discharges the gate automatically: `db_cert.prove_rec_partial` types the
motive and cases — including the motive-conversion bridges (`cC n ≡ Nat`)
generated by `prove_conv` + `deq_pi`/`deq_lam` — and `prove_ht` is a full
typing certifier for the fragment.  This is why each ι step now costs ~250
nodes instead of ~25: it carries its own typing derivation.

### General inductives (`induct.py`) — Nat is no longer special

`db.mm1` hard-wires Nat, but Nat is just *one* inductive.  `induct.py` is a
**generator**: given a spec (type former, constructors with their fields,
recursor) it emits the whole stock-MM0 axiom block — `term` decls, `shf`/`sub`
closure, typing (`ht_*`), and per-constructor **gated ι** — and registers the
inductive so `db_cert`'s certifier (`prove_ht` / `whnf` /
`prove_rec_partial_gen`) can typecheck and normalise terms over it.  This is
what `src/inductive.py` does internally, re-expressed as pure stock-MM0 axioms.

Scope: one universe, **with parameters** (uniform across constructors) **and
indices** (varying per constructor), **including the recursive + indexed case**
— so polymorphic `List`, the identity type `Eq` (J eliminator), and
length-indexed vectors `Vec` all work, alongside Bool and monomorphic ListNat.
Covers nullary/n-ary ctors and recursive + data fields.

The recursive+indexed case (`Vec`) is the subtle one: a recursive field can sit
at a *different* index than the constructor's output — `vcons`'s tail is
`xs : Vec A n` while `vcons : … → Vec A (succ n)`.  So each field carries its
own `rec_index_vals`, and the IH / iota recursive call use the *field's* index
(`n`), not the constructor's output index (`succ n`).  `Inductive.rec_calls()`
computes those concrete indices at reduction time.

**Correctness check:** regenerating Nat reproduces `db.mm1`'s hand-written
recursor type *verbatim*; polymorphic List matches an independently hand-built
de-Bruijn recursor type; Eq's type-former + ctor match hand-built de Bruijn
(`run_induct.py` asserts all of these).  The Eq and Vec *recursor* types are
validated end-to-end: mm0-c accepts the certified J- and vlength-computations,
which would fail if the (IH) index arithmetic were wrong.

Generated inductives + certified recursor computations (mm0-rs + mm0-c, all
exit 0; node counts read from the actual run):

| inductive | computation | nodes |
|---|---|---|
| `Bool` (2 nullary ctors)         | `not true = false` / `not false = true` | 90 / 90 |
| `ListNat` (nil; cons:Nat→L→L)    | `length [0] = 1`     | 383 |
| `ListNat`                        | `length [0,0,0] = 3` | 859 |
| `List A` (parametric)            | `length (List Nat) [0,0] = 2` | 1165 |
| `List A` — *same recursor, diff param* | `length (List Bool) [tt] = 1` | 725 |
| `Eq` (**indexed**; J eliminator) | `eqrec Nat 0 C 1 0 (refl Nat 0) = 1` | 341 |
| `Vec` (**recursive + indexed**)  | `vlength Nat [7,7] = 2` | 2581 |

The recursor types the generator builds, in de Bruijn:
- `Bool.rec : Π C:(Bool→Sort u), C true → C false → Π x, C x`
- `ListNat.rec : Π C:(L→Sort u), C nil → (Π h:Nat, Π t:L, C t → C (cons h t)) → Π x, C x`
- `List.rec : Π A:Sort1, Π C:(List A→Sort u), C(nil A) → (Π h:A, Π t:List A, C t → C(cons A h t)) → Π x, C x`
- `Eq.rec (J) : Π A:Sort1, Π a:A, Π C:(Π b:A, Eq A a b → Sort u), C a (refl A a) → Π b:A, Π h:Eq A a b, C b h`
- `Vec.rec : Π A:Sort1, Π C:(Π n:Nat, Vec A n → Sort u), C 0 (vnil A) → (Π n:Nat, Π a:A, Π xs:Vec A n, C n xs → C (succ n) (vcons A n a xs)) → Π n:Nat, Π x:Vec A n, C n x`

For an indexed inductive the motive abstracts over the indices **and** the
major (`C : Π b, Eq A a b → Sort u`), each constructor pins the indices to
specific values (`refl` sets `b := a`), and the gated ι fires when the major's
index pattern matches.

Parameters thread through the type former (`List : Sort1 → Sort1`), every
constructor (`cons : Π A, A → List A → List A`), and the recursor; recursive
occurrences reuse the same parameter, and `length (List Nat)` vs
`length (List Bool)` exercise the *same* generated recursor at two parameters.

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
python3 run_db_typed.py    # typed theorem via ht_conv   (de-Bruijn track)
python3 run_induct.py      # inductives: Bool, ListNat, List A, Eq, Vec (de-Bruijn)
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

## Speed: stock kernel (check) vs our verifier (compute)

`bench.py` runs Church multiplication `mul C_n C_n ⟹ C_(n²)` (pure β) through
both: our `src/mm0_verify._normalize` (computes the reduction — what our
trusted verifier does) vs generate-then-check with stock `mm0-c` (zero
computation in the kernel).

"our verifier" times are CPython, single-shot (so ±noise):

| n | result | our verifier | **mm0-c check** | gen (untrusted) | cert |
|---|---|---|---|---|---|
| 8  | C₆₄   | 2.5 ms | **1.2 ms** | 2.5 ms | 18 KB (2.1k nodes) |
| 16 | C₂₅₆  | 18 ms  | **1.8 ms** | 16 ms  | 34 KB (11k nodes) |
| 24 | C₅₇₆  | 72 ms  | **1.9 ms** | 61 ms  | 58 KB (31k nodes) |
| 28 | C₇₈₄  | 87 ms  | **1.5 ms** | 97 ms  | 76 KB (46k nodes) |
| 32 | C₁₀₂₄ | 133 ms | **1.9 ms** | 142 ms | 95 KB (66k nodes) |

Reading it honestly:
- **The stock kernel checks in ~1–2 ms and stays nearly flat** (it's
  process-startup-dominated — the actual proof-check is sub-millisecond),
  while our verifier's compute climbs ≈quadratically to 130 ms+ and keeps
  going.  So mm0-c is **2× (n=8) → 70× (n=32) faster to check, and pulling
  away** — an 815-line C program verifying every β-step vs our Python
  computing.  (PyPy narrows our side to ~3× at scale, with JIT-warmup noise.)
- **Certificates are modest here** (tens of KB) and **generation (untrusted
  Python) is comparable to just computing** — the expensive work moved out of
  the trusted base without exploding.
- **The win is architectural:** the correctness-critical surface shrinks to a
  tiny, fast, shared, soon-formally-verified kernel; computation lives in
  untrusted generation.  Ideal for "check a fixed corpus cheaply and
  trustably."

## Roadmap

1. ✅ **De-Bruijn prelude** (`db.mm1`) with `shift`/`subst1` as provable
   relations — reaches `1+1=2`.
2. ✅ **Core CIC typing judgment** (`ht_*`) + a typed theorem via `ht_conv` —
   `db.mm1` is now a sound-core trusted base, not just a reduction relation.
3. ✅ **Recursor typing + gated ι** (`ht_rec`, gated `deq_iota_*`) — ι is now
   a sound, type-preserving equality; the emitter discharges the typing gate
   automatically.  Nat is a typed primitive.
4. ✅ **General inductives — parameters, indices, recursive+indexed**
   (`induct.py`) — a generator emits the per-inductive axiom block + registers
   it; validated by reproducing Nat / List / Eq schemas; Bool, ListNat,
   `List A`, `Eq` (J), and `Vec` (recursive+indexed) all certified.
5. **Level equations + mutual inductives.**  The `lvl` equations
   (`lmax`/`limax` laws) our verifier normalises, and mutual inductive blocks
   (cross-recursors).
6. **δ.**  MM0 statement-level `def` unfolding for our `def`s.
7. 🟡 **Kernel integration (spike landed).**  `bridge.py` translates a real
   `src/expr.py` CIC term (already de Bruijn) into the `db_cert` AST, mapping
   `Nat.zero`/`Nat.succ`/`Nat.rec` → `tzero`/`tsucc`/`trec`.  `bridge_demo.py`
   takes an actual prelude `Nat.rec` term (`add 2 2`), bridges it, certifies
   the reduction, and **mm0-c accepts it** — the first genuine kernel→stock-MM0
   data point (not a hand-built db_cert demo).  Faithfulness is guarded by
   cross-checking the db_cert normal form against `src/kernel.py`'s own whnf.
   Spike result: `add 2 2 = 4`, kernel-nf and bridge-nf agree, **499 proof
   nodes, 13960-byte cert, mm0-rs + mm0-c both exit 0.**  Scope is the closed
   Nat fragment **plus parametric `List`** (`bridge.to_db` raises `Unsupported` on anything else, on
   purpose).  Still untouched: driving a whole `examples/*.lean` through
   parser→elaborator→kernel→bridge, and replacing `src/emitter.py`'s `de-refl`
   shortcut — that's what would move βιζ + shift/subst1 out of the *production*
   trusted base.

### Kernel-integration spike files
- `bridge.py` — `src.expr.Expr` (+`Level`) → `db_cert.T`, Nat fragment only.
- `bridge_demo.py` — builds a real `Nat.rec` term, bridges, certifies, checks
  with mm0-rs + mm0-c; cross-checks against the real kernel's whnf.  Writes a
  structured result to `/tmp/bridge_result.txt`.

## Files

**`lean.mm1` (named-binder) track:**
- `cert.py` — term AST (incl. `Imp`, `NatRec`), pretty-printer, Layer-1
  substitution certifier.
- `cert_beta.py` — Layer-2 typing certifier + whnf β-reducer.
- `cert_iota.py` — Layer-3 recursor reducer (`norm_rec`).
- `run_layer1.py`, `run_layer2.py`, `run_iota.py` — drivers.

**`db.mm1` (de-Bruijn) track — the real path:**
- `db.mm1` — de-Bruijn stock-MM0 prelude: `shift`/`subst1` as provable
  relations, untyped `deq` reduction, AND the core CIC typing judgment
  (`ht_*`).  Pure axioms (the trusted spec).
- `db_cert.py` — certifying evaluator: `prove_shf` / `prove_sub` /
  `prove_norm` (β + ι) + `prove_ht_nat` (numeral typing).
- `run_db.py` — concrete ground computations incl. `1+1=2`.
- `run_db_typed.py` — a typed theorem routing a reduction cert through
  `ht_conv`.
- `induct.py` — generator for general inductives (parameters + indices):
  spec → stock-MM0 axiom block + registry entry.
- `run_induct.py` — validates the generator against Nat, polymorphic List, and
  Eq; generates + certifies Bool, ListNat, `List A`, `Eq` (J), and `Vec`
  (recursive+indexed) computations.
- `bench.py` — speed benchmark (stock kernel check vs our verifier compute).

Generated output (`_gen_*.mm1`) is gitignored.


### Bridge widening: parametric List

The kernel-integration bridge (`bridge.py`) now also covers the prelude's
*parametric* `List`.  It maps `List` / `List.nil` / `List.cons` / `List.rec`
onto the `induct.generate(LIST)` block's `tlist` / `pnil` / `pcons` / `prec`.
The translation is purely structural: the real prelude already passes the type
parameter `A` as an ordinary application argument (`List.cons.{u} A …`,
`List.rec.{u} A …`), which is exactly `db_cert`'s param-as-arg convention, so
`to_db` simply drops the universe level and keeps the App spine — no new code
path beyond the name map.

`bridge_list_demo.py` builds real `List.rec` `length`-terms over `List Nat`,
certifies each reduction, and checks the certificate with **both** stock
checkers, with a faithfulness guard that cross-checks the `db_cert` normal form
against the real `src/kernel.py` whnf:

| computation | proof nodes | mm0-rs | mm0-c |
|---|---|---|---|
| `length [0] = 1`       | 725  | rc=0 | rc=0 |
| `length [0,0] = 2`     | 1165 | rc=0 | rc=0 |
| `length [0,0,0] = 3`   | 1639 | rc=0 | rc=0 |

(List block 1792 B · combined `.mm1` 45422 B · `.mmb` 33544 B.)  The
`length [0,0] = 2` certificate is **1165 nodes — identical to the hand-built
`run_induct.py` List demo**, cross-validating that the bridged real-prelude
term and the hand-authored `db_cert` term are the same proof.

Note: the real prelude *does* give `Bool` a genuine `Bool.rec` recursor, so Bool
is bridged too (`bridge_bool_demo.py`).  The prelude orders Bool
`false | true` (`Bool.false.index=0`, `Bool.true.index=1`); since a recursor
selects its minor by position, the demo registers a *prelude-ordered* Bool spec
(ctors `[bfalse, btrue]`) rather than `induct.BOOL`'s `[btrue, bfalse]`.
Verified: `not true=false` / `not false=true` / `not (not true)=true` →
**76 / 76 / 155 proof nodes, mm0-rs + mm0-c both rc=0**, faithfulness-guarded.

`bridge_eq_demo.py` reaches the first **indexed** family: `Eq` with the **J**
eliminator (2 params `A a`, 1 index `b`, single ctor `Eq.refl`).  The prelude's
`Eq.rec.{u,v} A a motive minor b major` is the standard
`params ++ motive ++ minors ++ indices ++ major` order, so the bridge stays
structural.  The canonical J computation `Eq.rec C base refl = base`:
`J 0/1/2 = 0/1/2` → **338 / 341 / 344 proof nodes, mm0-rs + mm0-c both rc=0**,
faithfulness-guarded against the real kernel.

`bridge_vec_demo.py` completes the spectrum with **`Vec`** -- length-indexed
vectors, **recursive *and* indexed**.  In `Vec.cons : (n)(a:A)(Vec A n) ->
Vec A (succ n)` the recursive tail sits at index `n` while the ctor outputs
`succ n`, so the recursor's IH uses the field's index, not the output's
(induct.py's `Fld.rec_index_vals`).  The prelude matched `induct.VEC` exactly
(ctor order, `Vec.cons` fields `[n,a,tail]`, `Vec.rec` arg order), so the
bridge stayed structural.  `vlength [0]/[0,0]/[0,0,0] = 1/2/3` →
**1551 / 2504 / 3569 proof nodes, mm0-rs + mm0-c both rc=0**, faithfulness-guarded.

With Vec the bridge spans the **entire inductive spectrum**: simple-recursive
(Nat), enumeration (Bool), parametric (List), indexed (Eq), and
recursive-indexed (Vec) -- every shape, real kernel term → 815-line C kernel.

### δ: definitional unfolding (no new trusted axiom)

`bridge_delta_demo.py` adds δ -- unfolding CIC `def`s.  The faithful trick: a
CIC `def d := body` is emitted as a stock-MM0 `def d: expr = $ body $;`, so
δ-unfolding becomes **mm0's own native def-unfold** -- the single proof-driven
step the verifier already does -- adding **zero** trusted axioms.  In the
certificate the δ step is even free: db_cert generates the proof about
`body @ args`, and mm0 accepts it for the `d @ args` theorem because `d ≡ body`
definitionally (`deq cnil d body` is literally `deq_refl`).

`bridge.register_def(env, name)` maps a prelude Definition to a sanitized mm0
identifier and registers its bridged body (recursively for nested defs);
`db_cert.gen_def_block()` emits the `def`s.  Real prelude defs `Nat.add` and
`Nat.pred` (bodies of pure Nat primitives) certify through δ+β+ι:

| computation | proof nodes | mm0-rs | mm0-c |
|---|---|---|---|
| `Nat.add 2 3 = 5` | 748 | rc=0 | rc=0 |
| `Nat.add 0 4 = 4` | 889 | rc=0 | rc=0 |
| `Nat.pred 3 = 2`  | 183 | rc=0 | rc=0 |
| `Nat.pred 0 = 0`  | 151 | rc=0 | rc=0 |

(faithfulness-guarded against the real kernel's whnf, which does its own δ.)

### Universe level equations

The kernel decides `Sort u ≡ Sort v` by normalising universe levels (the
semilattice lz / lS / lmax / limax) and comparing.  db.mm1 had the level
operations but no level-*equality* judgment, so universe-equal sorts could only
match when syntactically identical.  Added: a `leveq` judgment with the
semilattice laws (a fixed ~13-axiom spec block in db.mm1, like `ht_pi` -- refl /
sym / trans / congruence + max0l / max0r / maxS / maxid / imax0 / imaxS) and
`deq_sort : leveq a b -> deq g (esort a) (esort b)`.  `db_cert.prove_leveq`
normalises a closed level to its numeral with an explicit proof, hooked into
sort conversion.  `run_levels.py` certifies (mm0-rs + mm0-c both rc=0):

| level equation | result | proof nodes |
|---|---|---|
| `max 0 1`             | 1 | 11 |
| `max 1 1`             | 1 | 15 |
| `max 2 3` / `max 3 2` | 3 | 23 / 23 |
| `imax 2 0` (impredicative) | 0 | 11 |
| `imax 2 3`            | 3 | 25 |
| `max 1 (max 0 2)`     | 2 | 21 |
| `max u u = u` (open, parametric) | u | via `leveq_maxid` |

Closed levels (the bridge's current scope) normalise to numerals; open/param
levels beyond idempotence, and wiring this into a real kernel term whose
*conversion* needs a level equation, are the follow-ups.


## Capstone: a real `examples/*.lean` through stock mm0-c

`capstone_demo.py` closes the loop -- it runs a real source file through the
ACTUAL pipeline (`src.lean_parser.elaborate` = parser -> elaborator -> kernel),
then AUTO-DETECTS that file's `de-refl` obligations and discharges them with
stock mm0-c via the bridge -- **no `emitter.py`, no our `mm0_verify.py`**.

`examples/math.lean` has `example : Eq Nat (Nat.add 5 0) 5 := Eq.refl Nat 5`
(holds by computation).  `Eq.refl Nat 5 : Eq Nat 5 5` only typechecks because the
kernel reduces the left side; `emitter.py` discharges that with `(de-refl ...)`.
We instead elaborate the file and, for every decl whose type is `Eq Nat lhs rhs`
over closed Nat, register the defs `lhs` uses (`Nat.add`), bridge `lhs`, and emit
the explicit certificate `deq cnil lhs rhs` -- which both stock checkers accept:

| de-refl obligation (`math.lean`) | result | proof nodes | mm0-rs | mm0-c |
|---|---|---|---|---|
| `Nat.add 5 0` | 5 | 214 | rc=0 | rc=0 |
| `Nat.add 0 7` | 7 | 1474 | rc=0 | rc=0 |
| `Nat.add 5 3` | 8 | 814 | rc=0 | rc=0 |

(10 decls elaborated; 3 certified, 7 skipped; faithfulness-guarded against
`src/kernel.py` whnf.)  Honest scope: this is the de-refl-replacement path on
real elaborated source for the **direct-numeral Nat fragment**.  The nested
`Nat.add 7 (Nat.add 8 9) = 24` currently SKIPS -- the hard-wired Nat-iota gate
needs a numeral *major*, so nested def-apps don't reduce through it yet.  Full
βιζ-evaluator retirement (every decl, universe-polymorphic defs,
Bool/match/tactics, the whole suite) remains.
