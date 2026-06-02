"""Per-feature demo: UNIVERSE-POLYMORPHIC inductive used at a GENERIC level.

The last leg of the universe-polymorphism story (after poly defs and poly opaque
lemmas at a generic level).  A poly structure `Box.{u}` -- its constructor `Box.mk`
and projection `Box.val` -- is used inside a proof generic over u.

Unlike a def or opaque lemma (whose BODY mentions the level, so it needs a level-bound
mm0 def + a level-applied reference), an inductive's term constructors are
LEVEL-AGNOSTIC: the level rides the generated typing / iota axioms, exactly as for the
poly `Eq` (`refl_eq` carries no level arg; `ht_refl_eq (g)(v: lvl)` binds it).  So a
poly inductive at a generic level is simply registered ONCE, level-generically
(`register_inductive` with the inductive's OWN params kept -> lv_u, induct.generate
auto-detecting + binding them), and used by plain const names -- no level-application
node at all.  (The projection `Box.val` IS a poly def, so it rides the DefRef path.)

No trusted axiom, no trusted-base change.  Driven through the real proofterm_worker
(parser -> elaborator -> kernel -> bridge -> db_cert -> mm0-rs AND mm0-c).
"""
import os, re, sys, subprocess

HERE = os.path.dirname(os.path.abspath(__file__))

# Box.{u} is a poly structure; box_refl.{u} proves `Box.val (Box.mk a) = a` (the
# projection iota-reduces) GENERICALLY over u -- so Box / Box.mk / Box.val are all
# reached at the generic level u.
SRC = r"""
structure Box.{u} (A : Sort u) : Sort u where
  (val : A)
theorem box_refl.{u} (A : Sort u) (a : A) :
    Eq.{u} A (Box.val.{u} A (Box.mk.{u} A a)) a :=
  Eq.refl.{u} A a
"""


def main():
    path = "/tmp/poly_ind_gen_demo.lean"; open(path, "w").write(SRC)
    out = subprocess.run([sys.executable, f"{HERE}/proofterm_worker.py", path, "box_refl"],
                         capture_output=True, text=True)
    line = next((l for l in out.stdout.splitlines() if l.startswith("RESULT ")), "")
    print(SRC.strip())
    print("\n" + (line or out.stdout + out.stderr))

    mm1path = "/tmp/pt_poly_ind_gen_demo.lean_box_refl.mm1"
    ok = "status=certified" in line
    if os.path.exists(mm1path):
        mm1 = open(mm1path).read()
        genind   = bool(re.search(r"axiom ht_tBox_g\b|axiom ht_Box_g\b|tBox_g\b|Box_g\b", mm1))
        lvltyped = bool(re.search(r"\(v: lvl\)", mm1))      # generated typing axioms bind the level
        ptpoly   = bool(re.search(r"theorem pt \(lv_u: lvl\)", mm1))
        print(f"\n  poly inductive registered level-generically (Box_g):   {genind}")
        print(f"  generated typing axioms bind a level `(v: lvl)`:        {lvltyped}")
        print(f"  citing proof `box_refl` is itself .{{u}} poly:           {ptpoly}")

    print("\npoly inductive (GENERIC level) certified by BOTH checkers:", "OK" if ok else "FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
