"""Per-feature demo: WHOLE-ENVIRONMENT certification -- the stock base re-typechecks
arbitrary declarations, not just `Eq` goals.

Every earlier track certified EQUATIONS: de-refl leaves (`a ≡ b`) or whole proofs of
`Eq A lhs rhs`.  But a declaration's type can be ANY proposition -- an ordering
(`Nat.le a c`), a decidability (`Decidable c`), a typeclass method's result, ...  This
track types the decl's whole body against its stated type (`ht cnil <value> <type>`)
for ANY type, so the 815-line stock base re-verifies the kernel's typing of the *whole
environment*.  Faithful by construction: the term and type are the kernel's own.

The decls below are NON-equational on purpose (Nat.le transitivity is induction over an
INDEXED inductive; `choose` drives `Decidable.rec`).  Run `envcert_sweep.py` for the
full-corpus figure -- how many of ALL elaborated declarations the stock base re-types.

Each is run in a fresh proofterm_worker.py subprocess (the per-decl form of the
envcert worker): parser -> elaborator -> kernel -> bridge -> db_cert -> mm0-rs AND mm0-c.
"""
import os, re, sys, subprocess

HERE = os.path.dirname(os.path.abspath(__file__))

# (file, decl, the NON-Eq proposition it certifies)
TARGETS = [
    ("nat_le.lean", "Nat.le_refl",  "Nat.le n n                 -- reflexivity (a constructor)"),
    ("nat_le.lean", "Nat.le_trans", "a<=b -> b<=c -> a<=c       -- INDUCTION over an indexed inductive"),
    ("order.lean",  "succ_le",      "n<=m -> n<=succ m          -- a step lemma over Nat.le"),
    ("decidable.lean", "choose",    "Decidable c -> Nat         -- drives Decidable.rec"),
]


def main():
    print("Certifying NON-equational declarations by TYPING (ht cnil body type),"
          " via the real worker:\n")
    rows = []
    for fname, decl, desc in TARGETS:
        out = subprocess.run([sys.executable, f"{HERE}/proofterm_worker.py",
                              f"{HERE}/../../examples/{fname}", decl],
                             capture_output=True, text=True)
        line = next((l for l in out.stdout.splitlines() if l.startswith("RESULT ")), "")
        m = re.search(r"status=(\S+) nodes=(\d+) rs_rc=(-?\d+) cc_rc=(-?\d+)", line)
        if m and m.group(1) == "certified":
            rows.append(True)
            print(f"  OK    {decl:14s} {int(m.group(2)):>6d} nodes   {desc}")
        else:
            rows.append(False)
            print(f"  FAIL  {decl:14s}                {desc}\n        -> {line or out.stdout + out.stderr}")

    ok = sum(rows)
    print(f"\n{ok}/{len(rows)} non-equational declarations re-typechecked by BOTH stock checkers.")
    print("(Run envcert_sweep.py for the whole-corpus figure: every elaborated decl, not just these.)")
    sys.exit(0 if ok == len(rows) else 1)


if __name__ == "__main__":
    main()
