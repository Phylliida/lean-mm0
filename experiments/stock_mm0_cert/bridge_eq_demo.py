"""Widen the kernel-integration bridge to Eq -- the INDEXED identity type with
the J eliminator.  Takes REAL src/expr.py Eq.rec terms, bridges them to
db_cert, certifies the J reduction, and checks with stock mm0-rs + mm0-c.

Eq is the first *indexed* family the bridge reaches: 2 params (A, a), 1 index
(b), a single constructor Eq.refl (at index b := a), and the J recursor Eq.rec.
The probe confirmed the prelude's Eq.rec argument order is the standard

    Eq.rec.{u,v} A a motive minor b major

i.e. params ++ motive ++ minors ++ indices ++ major -- exactly db_cert's
general-iota layout -- so the bridge stays purely structural (params and the
index b are ordinary App args; to_db just drops the universe levels).

The canonical J computation: Eq.rec C base (Eq.refl) reduces to `base`.  We use
a constant motive (\\b h. Nat) so `base : Nat` and the result is that Nat.

Faithfulness guard: the db_cert normal form is cross-checked against the real
src/kernel.py whnf of the same term before certifying.
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

# Eq Nat 0 b   (b = nearest enclosing binder, BVar 0)
EqNat0 = lambda b: E.app_many(E.Const("Eq", (Z,)), Nat, Zero, b)
# motive C : (b:Nat) -> (h : Eq Nat 0 b) -> Type ; constant, returns Nat
motive = E.Lam("b", Nat, E.Lam("h", EqNat0(E.BVar(0)), Nat))
refl   = E.app_many(E.Const("Eq.refl", (Z,)), Nat, Zero)        # Eq.refl Nat 0 : 0 = 0

def J(base):
    # Eq.rec.{u,v} A a motive minor b major   (b := 0, major := refl 0=0)
    return E.app_many(E.Const("Eq.rec", (Z, Z)), Nat, Zero, motive, base, Zero, refl)


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

    block = induct.generate(induct.EQ)   # single ctor -> no ctor-order concern

    cases = [0, 1, 2]   # J C (base=n) refl  ->  n
    results = []
    for n in cases:
        term = J(numeral(n))

        knf = kernel_nf(K, term)
        LG("J base", n, "kernel_nf=", E.show(knf))
        assert numval(knf) == n, f"J base {n}: kernel says {E.show(knf)}"

        dterm = bridge.to_db(term)
        nf, conv = db_cert.prove_norm(dterm)
        conv = conv or "(deq_refl)"
        bridged_nf = db_cert.pp(nf)
        expected_nf = db_cert.pp(bridge.to_db(numeral(n)))
        LG("  bridge_nf=", bridged_nf, " expected=", expected_nf)
        assert bridged_nf == expected_nf, f"J base {n}: bridge nf {bridged_nf} != {expected_nf}"

        nodes = db_cert.proof_nodes(conv)
        results.append((n, db_cert.pp(dterm), bridged_nf, conv, nodes))

    prelude = open(f"{HERE}/db.mm1").read()
    thms = [f"theorem bridge_J_{n}: $ deq cnil {dpp} {nfpp} $ =\n'{conv};\n"
            for n, dpp, nfpp, conv, nodes in results]
    src = prelude + "\n" + block + "\n" + "\n".join(thms)
    open("/tmp/cert_eq.mm1", "w").write(src)

    r = subprocess.run([MM0RS, "compile", "/tmp/cert_eq.mm1",
                        "/tmp/cert_eq.mmb"], capture_output=True, text=True)
    rs_ok = (r.returncode == 0)
    LG("mm0-rs rc=", r.returncode)
    if not rs_ok:
        LG("---mm0-rs stdout---"); LG(r.stdout[-4000:])
        LG("---mm0-rs stderr---"); LG(r.stderr[-4000:])

    mmb_bytes = os.path.getsize("/tmp/cert_eq.mmb") if rs_ok else -1
    cc = subprocess.run([MM0C, "/tmp/cert_eq.mmb"], capture_output=True, text=True) \
         if rs_ok else None
    cc_rc = cc.returncode if cc else -1
    LG("mm0-c rc=", cc_rc)

    with open("/tmp/eq_bridge_result.txt", "w") as fh:
        fh.write("cases=%s\n" % ",".join("J%d=>%d" % (n, n) for n, *_ in results))
        for n, dpp, nfpp, conv, nodes in results:
            fh.write("J%d nodes=%d nf=%s\n" % (n, nodes, nfpp))
        fh.write("block_bytes=%d\n" % len(block))
        fh.write("mm1_bytes=%d\n" % len(src))
        fh.write("mm0rs_rc=%d\n" % r.returncode)
        fh.write("mm0c_rc=%d\n" % cc_rc)
        fh.write("mmb_bytes=%d\n" % mmb_bytes)
        fh.write("faithful=True\n")

    open("/tmp/eq_bridge.log", "w").write("\n".join(log) + "\n")
    print("done; rs_rc=%d cc_rc=%d" % (r.returncode, cc_rc))


if __name__ == "__main__":
    main()
