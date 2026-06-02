# Stock-MM0 coverage of the example suite

**How much of the real `examples/*.lean` suite does the stock-MM0 bridge already
cover?**  Rather than freeze an answer here (the figures shift every time the
bridge grows), this is measured by *running a script* — the numbers live in its
output, never in this file.

```
cd experiments/stock_mm0_cert
python3 coverage_sweep.py        # prints a per-file table + a fresh headline
```

## What it does

`coverage_sweep.py` runs `coverage_worker.py` over every `examples/*.lean`, one
**subprocess per file** so the bridge/db_cert globals (`CONST_MAP` / `MONO` /
`DEFS` / `TYCON` / …) reset between files and a crash on one file can't poison
the sweep.  For each file the worker:

1. runs the **real** pipeline — `src.lean_parser.elaborate` (parser → elaborator
   → kernel) — so we measure against actually-elaborated terms, not hand-built
   ones;
2. auto-detects every *Eq obligation*: an elaborated decl whose type is
   `Eq A lhs rhs` for **any** type `A` (Nat, Bool, List, Vec, …), possibly under a
   free-variable Π-telescope or a universe parameter;
3. certifies it through **stock mm0-c** by one of two routes, picked by the real
   kernel:
   - if the two sides **convert** (a `by rfl` / `Eq.refl` leaf), it bridges both
     and certifies `deq <ctx> lhs rhs` by conversion — with the db_cert normal form
     cross-checked against `src/kernel.py`'s own whnf (the faithfulness guard);
   - if they **don't** (the obligation needs a real proof — induction, case
     analysis, transport), it types the decl's **whole proof term** against its
     stated type, `ht cnil <value> <type>` (the proof-term track), so the proof is
     faithful by construction (it is the kernel's own elaborated term and type);
4. counts each obligation as *certified* or *skipped* (with a reason), catching
   any per-obligation error so one bad goal never aborts the file.

The worker prints one machine-readable `RESULT …` line per file; the driver
aggregates them into a table and a headline, and **asserts the invariant** that
every file with ≥1 certified obligation passes *both* mm0-rs and mm0-c (it exits
non-zero if that ever breaks).

## How to read the outcome

- **Files that don't elaborate here** reference a declaration the *standalone*
  `build_stdlib` baseline doesn't provide (the real test suite builds a richer
  shared env).  That's a *harness/stdlib gap, not a bridge limitation* — each
  such file's `RESULT` line names the first missing decl.
- **Skipped obligations** are honest scope.  The bridge targets *closed-Nat*
  computational goals; it does not (yet) cover proofs with free variables
  (induction steps, abstract lemmas → `nf-mismatch` / `ValueError`) or terms
  outside the bridged `Nat`/`Bool`/`List`/`Eq`/`Vec` fragment (`unsup`).
- **Certified obligations** are the payoff: real computational `Eq Nat` goals
  from real elaborated source, discharged end-to-end by the 815-line C kernel,
  each one faithfulness-guarded.

The point of this experiment was never a coverage *percentage* — it was to show
the stock trusted base *can* discharge these obligations at all.  Run the sweep
when you want the current spread.
