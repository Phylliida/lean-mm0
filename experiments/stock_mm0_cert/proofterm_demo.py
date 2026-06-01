"""Per-feature demo: certify whole PROOF TERMS that USE the induction hypothesis.

The de-refl track certifies the `Eq.refl` / `by rfl` LEAVES of a proof (a
conversion `a ≡ b`).  This track certifies an entire proof TERM by TYPING it
against its stated type (`ht cnil <body> <type>`) -- so it reaches proofs built by
`Nat.rec` whose step case transports along the IH via `Eq.rec`, case analysis on
Bool, injectivity via transport, etc.  These are genuine theorems, not rfl leaves.

Each proof is run in a fresh `proofterm_worker.py` subprocess (parser -> elaborator
-> kernel -> bridge -> db_cert.prove_ht -> mm0-rs AND mm0-c).  Scope: closed,
monomorphic proofs within the bridged fragment (delta-inlined helper lemmas are
fine -- add_comm inlines zero_add + succ_add).
"""
import os, re, sys, subprocess

HERE = os.path.dirname(os.path.abspath(__file__))

# (file, decl, what it demonstrates)
TARGETS = [
    ("math.lean",    "zero_add",     "add 0 n = n           -- induction, step uses IH"),
    ("math.lean",    "succ_add",     "add (S m) n = S(add m n) -- induction + transport"),
    ("math.lean",    "add_comm",     "add m n = add n m     -- THE theorem; inlines zero_add+succ_add"),
    ("bool_ops.lean","Bool.not_not", "not (not b) = b       -- case analysis on Bool"),
    ("nat_inj.lean", "succ_inj",     "S m = S n -> m = n     -- injectivity via transport"),
]


def main():
    print("Certifying whole proof terms by TYPING (ht cnil body type), via the real worker:\n")
    rows = []
    for fname, decl, desc in TARGETS:
        out = subprocess.run([sys.executable, f"{HERE}/proofterm_worker.py",
                              f"{HERE}/../../examples/{fname}", decl],
                             capture_output=True, text=True)
        line = next((l for l in out.stdout.splitlines() if l.startswith("RESULT ")), "")
        m = re.search(r"status=(\S+) nodes=(\d+) rs_rc=(-?\d+) cc_rc=(-?\d+)", line)
        if m and m.group(1) == "certified":
            rows.append((decl, int(m.group(2)), True))
            print(f"  OK    {decl:14s} {int(m.group(2)):>7d} nodes   {desc}")
        else:
            rows.append((decl, 0, False))
            print(f"  FAIL  {decl:14s}                 {desc}\n        -> {line or out.stdout + out.stderr}")

    ok = sum(1 for _n, _c, good in rows if good)
    print(f"\n{ok}/{len(rows)} whole proof terms certified by BOTH stock checkers.")
    sys.exit(0 if ok == len(rows) else 1)


if __name__ == "__main__":
    main()
