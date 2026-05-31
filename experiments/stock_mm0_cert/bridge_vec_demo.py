"""Complete the inductive spectrum: widen the kernel bridge to Vec -- the
length-indexed vector, RECURSIVE *and* INDEXED.  Takes REAL src/expr.py
Vec.rec terms (vlength), bridges them to db_cert, certifies the reduction, and
checks with stock mm0-rs + mm0-c.

Vec is the subtle case: in `Vec.cons : (n) (a:A) (Vec A n) -> Vec A (succ n)`
the recursive tail sits at index n, but the constructor outputs index succ n,
so the recursor's IH / the iota recursive call must use the FIELD's index n,
not the output's succ n.  induct.py already models this (Fld.rec_index_vals),
and the probe confirmed the prelude matches induct.VEC exactly:
  - ctors [Vec.nil, Vec.cons]                       == [vnil, vcons]
  - Vec.cons fields [n:Nat, a:A, t:Vec A n]         == induct.VEC vcons
  - Vec.rec args [A, motive, m_nil, m_cons, n, vec] == params ++ motive
                                                       ++ minors ++ index ++ major
so the bridge stays purely structural and reuses the shared induct.VEC spec.

Faithfulness guard: db_cert normal form cross-checked against src/kernel.py whnf.
"""
import os, sys, subprocess

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
for p in (HERE, ROOT):
    if p not in sys.path:
        sys.path.insert(0, p)

from src import expr as E
from src.levels import LZero
from src.env import Env
from src.kernel import Kernel, LocalCtx
from src.prelude_decls import build_stdlib

import bridge
import db_cert
import induct

MM0   = "/home/bepis/prog/scientific-computing/mm0"
MM0RS = f"{MM0}/mm0-rs/target/release/mm0-rs"
MM0C  = f"{MM0}/mm0-c/mm0-c-np"

Z    = LZero()
Nat  = E.Const("Nat", ())
Zero = E.Const("Nat.zero", ())
Succ = lambda x: E.App(E.Const("Nat.succ", ()), x)

def numeral(n):
    t = Zero
    for _ in range(n):
        t = Succ(t)
    return t

def numval(e):
    n = 0
    while isinstance(e, E.App) and isinstance(e.fn, E.Const) and e.fn.name == "Nat.succ":
        n += 1; e = e.arg
    return n if (isinstance(e, E.Const) and e.name == "Nat.zero") else None

# Vec A n   (one universe level, like Vec.nil/Vec.cons)
VecT = lambda A, n: E.app_many(E.Const("Vec", (Z,)), A, n)
Vnil  = E.app_many(E.Const("Vec.nil", (Z,)), Nat)                      # Vec Nat 0
# Vec.cons A n a tail
Vcons = lambda n, a, tail: E.app_many(E.Const("Vec.cons", (Z,)), Nat, n, a, tail)

def vec_lit(xs):
    """[x0,..,x_{k-1}] : Vec Nat k, built innermost-out; tail length = i."""
    v = Vnil
    for i, x in enumerate(reversed(xs)):     # i = current tail length
        v = Vcons(numeral(i), x, v)
    return v

# vlength via Vec.rec, constant motive (\n v. Nat):
#   m_nil  = 0
#   m_cons = \n a tail ih. succ ih
motive = E.Lam("n", Nat, E.Lam("v", VecT(Nat, E.BVar(0)), Nat))
m_nil  = Zero
m_cons = E.Lam("n", Nat,
           E.Lam("a", Nat,
             E.Lam("tail", VecT(Nat, E.BVar(1)),    # n is BVar1 (binders: n, a)
               E.Lam("ih", Nat,                     # ih : motive n tail = Nat
                 Succ(E.BVar(0))))))                # succ ih

def vlength(xs):
    # Vec.rec.{u,v} A motive m_nil m_cons n vec
    return E.app_many(E.Const("Vec.rec", (Z, Z)),
                      Nat, motive, m_nil, m_cons, numeral(len(xs)), vec_lit(xs))


def kernel_nf(K, e, ctx=None):
    ctx = ctx or LocalCtx()
    e = K.whnf(e, ctx)
    if isinstance(e, E.App):
        return E.App(kernel_nf(K, e.fn, ctx), kernel_nf(K, e.arg, ctx))
    if isinstance(e, E.Lam):
        return E.Lam(e.binder, kernel_nf(K, e.dom, ctx), e.body)
    return e


def main():
    log = []
    LG = lambda *a: log.append(" ".join(str(x) for x in a))

    env = Env(); build_stdlib(env)
    K = Kernel(env)

    block = induct.generate(induct.VEC)   # ctors [vnil, vcons] match the prelude

    cases = [[Zero], [Zero, Zero], [Zero, Zero, Zero]]   # vlength -> 1, 2, 3
    results = []
    for xs in cases:
        term = vlength(xs)
        expected = len(xs)

        knf = kernel_nf(K, term)
        LG("vlength len", len(xs), "kernel_nf=", E.show(knf))
        assert numval(knf) == expected, f"len {len(xs)}: kernel says {E.show(knf)}"

        dterm = bridge.to_db(term)
        nf, conv = db_cert.prove_norm(dterm)
        conv = conv or "(deq_refl)"
        bridged_nf = db_cert.pp(nf)
        expected_nf = db_cert.pp(bridge.to_db(numeral(expected)))
        LG("  bridge_nf=", bridged_nf, " expected=", expected_nf)
        assert bridged_nf == expected_nf, f"len {len(xs)}: bridge nf {bridged_nf} != {expected_nf}"

        nodes = db_cert.proof_nodes(conv)
        results.append((len(xs), db_cert.pp(dterm), bridged_nf, conv, nodes))

    prelude = open(f"{HERE}/db.mm1").read()
    thms = [f"theorem bridge_vlen_{n}: $ deq cnil {dpp} {nfpp} $ =\n'{conv};\n"
            for n, dpp, nfpp, conv, nodes in results]
    src = prelude + "\n" + block + "\n" + "\n".join(thms)
    open("/tmp/cert_vec.mm1", "w").write(src)

    r = subprocess.run([MM0RS, "compile", "/tmp/cert_vec.mm1",
                        "/tmp/cert_vec.mmb"], capture_output=True, text=True)
    rs_ok = (r.returncode == 0)
    LG("mm0-rs rc=", r.returncode)
    if not rs_ok:
        LG("---mm0-rs stdout---"); LG(r.stdout[-4000:])
        LG("---mm0-rs stderr---"); LG(r.stderr[-4000:])

    mmb_bytes = os.path.getsize("/tmp/cert_vec.mmb") if rs_ok else -1
    cc = subprocess.run([MM0C, "/tmp/cert_vec.mmb"], capture_output=True, text=True) \
         if rs_ok else None
    cc_rc = cc.returncode if cc else -1
    LG("mm0-c rc=", cc_rc)

    with open("/tmp/vec_bridge_result.txt", "w") as fh:
        fh.write("cases=%s\n" % ",".join("len%d=>%d" % (n, n) for n, *_ in results))
        for n, dpp, nfpp, conv, nodes in results:
            fh.write("len%d nodes=%d nf=%s\n" % (n, nodes, nfpp))
        fh.write("block_bytes=%d\n" % len(block))
        fh.write("mm1_bytes=%d\n" % len(src))
        fh.write("mm0rs_rc=%d\n" % r.returncode)
        fh.write("mm0c_rc=%d\n" % cc_rc)
        fh.write("mmb_bytes=%d\n" % mmb_bytes)
        fh.write("faithful=True\n")

    open("/tmp/vec_bridge.log", "w").write("\n".join(log) + "\n")
    print("done; rs_rc=%d cc_rc=%d" % (r.returncode, cc_rc))


if __name__ == "__main__":
    main()
