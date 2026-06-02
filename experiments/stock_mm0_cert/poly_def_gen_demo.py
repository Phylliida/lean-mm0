"""Per-feature demo: UNIVERSE-POLYMORPHIC def used at a GENERIC level.

The def analogue of poly_opaque_gen_demo.py.  A poly proof `use_sym.{u}` uses a poly
DEF `mysym.{u}` at the GENERIC level u, so the def can never be monomorphised.  Unlike
an opaque lemma (a `theorem`, typed once by an htop reference), a `def` is delta-
TRANSPARENT: it is emitted as a level-bound mm0 def `mysym_g (lv_u: lvl)`, and a use is
a `DefRef` -> `(mysym_g lv_u)` that UNFOLDS to its body with the use-site level
substituted (typed via the unfolded body; MM0 delta-matches the folded reference).

This is what the coverage sweep's last `unsup:u` skips needed: level-poly theorems
whose proofs drive `Eq.symm` / `Eq.trans` (poly defs) at a generic level.  No trusted
axiom, no trusted-base change: db.mm1 byte-identical; the level binder lives on the
generated def, checked like everything else.

Driven through the real proofterm_worker (parser -> elaborator -> kernel -> bridge
-> db_cert -> mm0-rs AND mm0-c).
"""
import os, re, sys, subprocess

HERE = os.path.dirname(os.path.abspath(__file__))

# mysym is a poly DEF (delta-transparent); use_sym.{u} uses it at the GENERIC level u,
# twice.  Contrast poly_opaque_gen_demo, where the cited lemma is a `theorem` (opaque).
SRC = r"""
def mysym.{u} (A : Sort u) (a b : A) (h : Eq.{u} A a b) : Eq.{u} A b a :=
  @Eq.rec.{u, 0} A a
    (fun (x : A) (_ : Eq.{u} A a x) => Eq.{u} A x a)
    (Eq.refl.{u} A a)
    b h
theorem use_sym.{u} (A : Sort u) (a b : A) (h : Eq.{u} A a b) : Eq.{u} A a b :=
  mysym.{u} A b a (mysym.{u} A a b h)
"""


def main():
    path = "/tmp/poly_def_gen_demo.lean"; open(path, "w").write(SRC)
    out = subprocess.run([sys.executable, f"{HERE}/proofterm_worker.py", path, "use_sym"],
                         capture_output=True, text=True)
    line = next((l for l in out.stdout.splitlines() if l.startswith("RESULT ")), "")
    print(SRC.strip())
    print("\n" + (line or out.stdout + out.stderr))

    mm1path = "/tmp/pt_poly_def_gen_demo.lean_use_sym.mm1"
    ok = "status=certified" in line
    if os.path.exists(mm1path):
        mm1 = open(mm1path).read()
        lvbound = bool(re.search(r"def mysym_g \(lv_u: lvl\)", mm1))
        ptpoly  = bool(re.search(r"theorem pt \(lv_u: lvl\)", mm1))
        refs    = len(re.findall(r"\(mysym_g lv_u\)", mm1))
        print(f"\n  poly def is a LEVEL-bound mm0 def `mysym_g (lv_u: lvl)`: {lvbound}")
        print(f"  citing proof `use_sym` is itself .{{u}} poly:           {ptpoly}")
        print(f"  used as a DefRef `(mysym_g lv_u)` (delta-transparent):  {refs} time(s)")

    print("\npoly def (GENERIC level) certified by BOTH checkers:", "OK" if ok else "FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
