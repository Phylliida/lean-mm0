"""Per-feature demo: UNIVERSE-POLYMORPHIC opaque lemma cited at a CONCRETE level.

The opaque-lemma machinery (opaque_demo.py) certified a *monomorphic* `theorem`
cited by reference.  This extends it to a UNIVERSE-POLYMORPHIC lemma: a poly
`theorem my_eq_symm.{u}` cited at a concrete use-site level (`.{1}`) is
MONOMORPHISED -- its body/type level-instantiated into a closed term and registered
as a distinct closed opaque lemma per level-tag (`my_eq_symm_1`) -- exactly as a
poly *def* is monomorphised for delta.  The monomorphised lemma rides every existing
closed-opaque path: typed ONCE via a `htop_my_eq_symm_1 (g: ctx)` theorem, and every
USE (here TWICE -- symm of symm) types by REFERENCE to it, never re-typing the body.

No trusted axiom, no trusted-base change: the lemma's typing is PROVED once, and the
context-polymorphic `htop` serves every use site -- the same shape as the monomorphic
case, reached for a poly lemma by monomorphising at the use-site level.  (Citing a
poly lemma at a *generic* level, inside another poly proof, is the next step -- its
htop needs level binders.)

Driven through the real proofterm_worker (parser -> elaborator -> kernel -> bridge
-> db_cert -> mm0-rs AND mm0-c).
"""
import os, re, sys, subprocess

HERE = os.path.dirname(os.path.abspath(__file__))

# my_eq_symm is UNIVERSE-POLYMORPHIC (.{u}); symm_twice cites it at the concrete
# level 1, TWICE.  Both citations resolve to the SAME monomorphised opaque lemma
# (my_eq_symm_1), typed once via htop_my_eq_symm_1 and referenced twice.
SRC = r"""
theorem my_eq_symm.{u} (A : Sort u) (a b : A) (h : Eq.{u} A a b) : Eq.{u} A b a :=
  @Eq.rec.{u, 0} A a
    (fun (x : A) (_ : Eq.{u} A a x) => Eq.{u} A x a)
    (Eq.refl.{u} A a)
    b h
def symm_twice (a b : Nat) (h : Eq.{1} Nat a b) : Eq.{1} Nat a b :=
  my_eq_symm.{1} Nat b a (my_eq_symm.{1} Nat a b h)
"""


def nodes_of(mm1, thm):
    m = re.search(r"theorem %s[^=]*=\s*'(.*?);" % re.escape(thm), mm1, re.S)
    return len(re.findall(r"[A-Za-z_]\w*", m.group(1))) if m else None


def main():
    path = "/tmp/poly_opaque_demo.lean"; open(path, "w").write(SRC)
    out = subprocess.run([sys.executable, f"{HERE}/proofterm_worker.py", path, "symm_twice"],
                         capture_output=True, text=True)
    line = next((l for l in out.stdout.splitlines() if l.startswith("RESULT ")), "")
    print(SRC.strip())
    print("\n" + (line or out.stdout + out.stderr))

    mm1path = "/tmp/pt_poly_opaque_demo.lean_symm_twice.mm1"
    ok = "status=certified" in line
    if os.path.exists(mm1path):
        mm1 = open(mm1path).read()
        # ONE monomorphised opaque lemma, typed once; cited twice in the proof.
        ndefs = len(re.findall(r"^def my_eq_symm_1:", mm1, re.M))
        lemma = nodes_of(mm1, "htop_my_eq_symm_1")
        uses  = len(re.findall(r"\(htop_my_eq_symm_1\)", mm1))
        proof = nodes_of(mm1, "pt")
        print(f"\n  poly `my_eq_symm.{{u}}` monomorphised at .{{1}}:  {ndefs} closed def(s)")
        print(f"  typed ONCE (htop_my_eq_symm_1):              {lemma} nodes")
        print(f"  cited BY REFERENCE in `symm_twice`:          {uses} time(s)")
        print(f"  `symm_twice` proof (cites my_eq_symm x2):    {proof} nodes")
        if lemma:
            print(f"  inlining both copies would be ~{2*lemma}+ nodes "
                  f"-> opacity holds for a poly lemma too.")

    print("\npoly opaque-lemma (concrete level) certified by BOTH checkers:",
          "OK" if ok else "FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
