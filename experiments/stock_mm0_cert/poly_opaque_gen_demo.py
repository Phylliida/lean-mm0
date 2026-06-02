"""Per-feature demo: UNIVERSE-POLYMORPHIC opaque lemma cited at a GENERIC level.

This is the deep case the opaque-lemma arc was building toward.  poly_opaque_demo.py
cited a poly `theorem` at a CONCRETE level (monomorphised away).  Here a poly proof
`symm_symm.{u}` cites a poly lemma `my_eq_symm.{u}` at the GENERIC level `u` -- so the
lemma can never be monomorphised; its typing must be proved ONCE, generically over all
universes, and referenced.

The mechanism is the exact DUAL, for LEVELS, of the original opacity trick.  A closed
body's typing proof is CONTEXT-polymorphic (the context `g` stays a metavariable), so
one `htop (g: ctx)` serves every use site.  A *generic* body's typing proof is in
addition LEVEL-polymorphic: db.mm1's `ht_sort`/`deq_refl` already bind a level
metavariable, so the SAME prove_ht proof, with `(lv_u: lvl)` bound on the htop, types
the lemma at every use level.  The lemma is emitted as a level-bound def
`my_eq_symm_g (lv_u: lvl)`, the htop as
`htop_my_eq_symm_g (lv_u: lvl) (g: ctx): ht g (my_eq_symm_g lv_u) <type>`, and every
use is a `(my_eq_symm_g lv_u)` whose level MM0 unifies syntactically against the htop.

No trusted axiom, no trusted-base change: db.mm1 is byte-identical; the level binder
lives on the GENERATED def/htop, checked like everything else.

Driven through the real proofterm_worker (parser -> elaborator -> kernel -> bridge
-> db_cert -> mm0-rs AND mm0-c).
"""
import os, re, sys, subprocess

HERE = os.path.dirname(os.path.abspath(__file__))

# BOTH the lemma and its caller are universe-polymorphic (.{u}); symm_symm cites
# my_eq_symm at the GENERIC level u, twice (symm of symm = identity on the proof).
SRC = r"""
theorem my_eq_symm.{u} (A : Sort u) (a b : A) (h : Eq.{u} A a b) : Eq.{u} A b a :=
  @Eq.rec.{u, 0} A a
    (fun (x : A) (_ : Eq.{u} A a x) => Eq.{u} A x a)
    (Eq.refl.{u} A a)
    b h
theorem symm_symm.{u} (A : Sort u) (a b : A) (h : Eq.{u} A a b) : Eq.{u} A a b :=
  my_eq_symm.{u} A b a (my_eq_symm.{u} A a b h)
"""


def nodes_of(mm1, thm):
    m = re.search(r"theorem %s[^=]*=\s*'(.*?);" % re.escape(thm), mm1, re.S)
    return len(re.findall(r"[A-Za-z_]\w*", m.group(1))) if m else None


def main():
    path = "/tmp/poly_opaque_gen_demo.lean"; open(path, "w").write(SRC)
    out = subprocess.run([sys.executable, f"{HERE}/proofterm_worker.py", path, "symm_symm"],
                         capture_output=True, text=True)
    line = next((l for l in out.stdout.splitlines() if l.startswith("RESULT ")), "")
    print(SRC.strip())
    print("\n" + (line or out.stdout + out.stderr))

    mm1path = "/tmp/pt_poly_opaque_gen_demo.lean_symm_symm.mm1"
    ok = "status=certified" in line
    if os.path.exists(mm1path):
        mm1 = open(mm1path).read()
        lvbound = bool(re.search(r"def my_eq_symm_g \(lv_u: lvl\)", mm1)) and \
                  bool(re.search(r"theorem htop_my_eq_symm_g \(lv_u: lvl\) \(g: ctx\)", mm1))
        folded  = "ht g (my_eq_symm_g lv_u)" in mm1
        ptpoly  = bool(re.search(r"theorem pt \(lv_u: lvl\)", mm1))
        lemma   = nodes_of(mm1, "htop_my_eq_symm_g")
        uses    = len(re.findall(r"\(htop_my_eq_symm_g\)", mm1))
        proof   = nodes_of(mm1, "pt")
        print(f"\n  lemma is a LEVEL-bound def + htop (lv_u: lvl):  {lvbound}")
        print(f"  htop states the folded `(my_eq_symm_g lv_u)`:  {folded}")
        print(f"  citing proof `symm_symm` is itself .{{u}} poly:  {ptpoly}")
        print(f"  typed ONCE, generically (htop_my_eq_symm_g):   {lemma} nodes")
        print(f"  cited BY REFERENCE at the generic level:       {uses} time(s)")
        print(f"  `symm_symm` proof:                             {proof} nodes")

    print("\npoly opaque-lemma (GENERIC level) certified by BOTH checkers:",
          "OK" if ok else "FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
