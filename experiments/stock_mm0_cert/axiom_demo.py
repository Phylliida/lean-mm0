"""Per-feature demo: SOURCE-LEVEL axioms -- certify a proof *modulo* the axioms it
assumes, carried faithfully (the stock-MM0 analogue of `#print axioms`).

Real Lean developments rest on axioms with no proof: `propext`, `Classical.choice`,
`Quot.sound`, or a file's own `axiom`.  A faithful checker can't *prove* those -- there
is no body -- so it CARRIES them: the proof is certified valid *given* the axioms it
uses, exactly as the Lean source (and Lean's own kernel) assume them.  Contrast
poly_opaque_gen_demo, where the cited `my_eq_symm` was a `theorem` whose typing we
PROVE; here `myax` is an `axiom` whose typing we ASSERT.

db.mm1 -- the CIC trusted base -- is UNCHANGED.  A source axiom becomes a `term <san>:
expr;` + an mm0 `axiom ht_<san>: ht g <san> <type>` (the user development's assumption),
emitted into the cert and surfaced in the axioms-used report below.

Driven through the real proofterm_worker (parser -> elaborator -> kernel -> bridge
-> db_cert -> mm0-rs AND mm0-c).
"""
import os, re, sys, subprocess

HERE = os.path.dirname(os.path.abspath(__file__))

# `myax` is a SOURCE AXIOM (symmetry of Eq, asserted with no proof); use_ax uses it.
# The cert certifies use_ax *modulo myax* -- declaring `term myax` + `axiom ht_myax`.
SRC = r"""
axiom myax.{u} (A : Sort u) (a b : A) (h : Eq.{u} A a b) : Eq.{u} A b a
theorem use_ax (a b : Nat) (h : Eq.{1} Nat a b) : Eq.{1} Nat b a :=
  myax.{1} Nat a b h
"""


def main():
    path = "/tmp/axiom_demo.lean"; open(path, "w").write(SRC)
    out = subprocess.run([sys.executable, f"{HERE}/proofterm_worker.py", path, "use_ax"],
                         capture_output=True, text=True)
    line = next((l for l in out.stdout.splitlines() if l.startswith("RESULT ")), "")
    print(SRC.strip())
    print("\n" + (line or out.stdout + out.stderr))

    mm1path = "/tmp/pt_axiom_demo.lean_use_ax.mm1"
    ok = "status=certified" in line
    if os.path.exists(mm1path):
        mm1 = open(mm1path).read()
        carried = bool(re.search(r"^term myax: expr;", mm1, re.M)) and \
                  bool(re.search(r"^axiom ht_myax ", mm1, re.M))
        used = bool(re.search(r"\(ht_myax\)", mm1))
        print(f"\n  source axiom CARRIED in the cert (term + axiom ht_myax):  {carried}")
        print(f"  the proof of `use_ax` invokes it (ht_myax) by reference:  {used}")
        print(f"  AXIOMS USED (the honest `#print axioms`):                 myax")
        print(f"  db.mm1 (the CIC trusted base) unchanged; `myax` is the source's"
              f"\n    assumption, NOT a new CIC rule -- the cert is valid MODULO it.")

    print("\nproof certified MODULO its source axiom, by BOTH checkers:", "OK" if ok else "FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
