"""Widen the kernel-integration bridge to Bool: take REAL src/expr.py terms
built from the prelude's `Bool.rec` (e.g. `not`), bridge them to db_cert,
certify the reductions, and check with stock mm0-rs + mm0-c.

Bool is the simplest non-Nat inductive (no params, no indices, two nullary
ctors) -- but it exposes a subtlety List did not: CONSTRUCTOR ORDER.  A
recursor selects its minor by ctor position, and the real prelude orders Bool
as `false | true` (Bool.false.index=0, Bool.true.index=1).  induct.BOOL uses
the opposite order ([btrue, bfalse]), so we register our OWN prelude-ordered
Bool spec here (ctors [bfalse, btrue]) instead of induct.BOOL -- leaving the
shared spec and its run_induct.py demo untouched.

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
from induct import Inductive, Ctor

MM0   = "/home/bepis/prog/scientific-computing/mm0"
MM0RS = f"{MM0}/mm0-rs/target/release/mm0-rs"
MM0C  = f"{MM0}/mm0-c/mm0-c-np"

# Prelude-ordered Bool: false=0, true=1 (matches Bool.false.index / Bool.true.index).
# Same names/tycon/recursor as induct.BOOL, just the constructor order the real
# prelude uses -- so the bridged term's minors line up with db_cert's ctor index.
BOOL_P = Inductive("tbool", "(lS lz)", [
    Ctor("bfalse", ()),
    Ctor("btrue", ()),
], "brec")

Z    = LZero()
Bool = E.Const("Bool", ())
T    = E.Const("Bool.true", ())
F    = E.Const("Bool.false", ())
# Bool.rec arg order: motive ++ [minor_false, minor_true] ++ major  (ctor index order)
motive = E.Lam("_", Bool, Bool)                                  # \_:Bool. Bool
NOT = lambda x: E.app_many(E.Const("Bool.rec", (Z,)), motive, T, F, x)  # not x


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

    block = induct.generate(BOOL_P)   # register prelude-ordered Bool + emit block

    # (label, term, expected prelude Const)
    cases = [
        ("not_true",      NOT(T),         F),   # not true  = false
        ("not_false",     NOT(F),         T),   # not false = true
        ("not_not_true",  NOT(NOT(T)),    T),   # not (not true) = true   (2 iota steps)
    ]

    results = []
    for label, term, expected in cases:
        knf = kernel_nf(K, term)
        LG(label, "kernel_nf=", E.show(knf))
        assert knf == expected, f"{label}: kernel says {E.show(knf)}, expected {E.show(expected)}"

        dterm = bridge.to_db(term)
        nf, conv = db_cert.prove_norm(dterm)
        conv = conv or "(deq_refl)"
        bridged_nf = db_cert.pp(nf)
        expected_nf = db_cert.pp(bridge.to_db(expected))
        LG("  bridge_nf=", bridged_nf, " expected=", expected_nf)
        assert bridged_nf == expected_nf, f"{label}: bridge nf {bridged_nf} != {expected_nf}"

        nodes = db_cert.proof_nodes(conv)
        results.append((label, db_cert.pp(dterm), bridged_nf, conv, nodes))

    prelude = open(f"{HERE}/db.mm1").read()
    thms = [f"theorem bridge_{label}: $ deq cnil {dpp} {nfpp} $ =\n'{conv};\n"
            for label, dpp, nfpp, conv, nodes in results]
    src = prelude + "\n" + block + "\n" + "\n".join(thms)
    open("/tmp/cert_bool.mm1", "w").write(src)

    r = subprocess.run([MM0RS, "compile", "/tmp/cert_bool.mm1",
                        "/tmp/cert_bool.mmb"], capture_output=True, text=True)
    rs_ok = (r.returncode == 0)
    LG("mm0-rs rc=", r.returncode)
    if not rs_ok:
        LG("---mm0-rs stdout---"); LG(r.stdout[-4000:])
        LG("---mm0-rs stderr---"); LG(r.stderr[-4000:])

    mmb_bytes = os.path.getsize("/tmp/cert_bool.mmb") if rs_ok else -1
    cc = subprocess.run([MM0C, "/tmp/cert_bool.mmb"], capture_output=True, text=True) \
         if rs_ok else None
    cc_rc = cc.returncode if cc else -1
    LG("mm0-c rc=", cc_rc)

    with open("/tmp/bool_bridge_result.txt", "w") as fh:
        fh.write("cases=%s\n" % ",".join(label for label, *_ in results))
        for label, dpp, nfpp, conv, nodes in results:
            fh.write("%s nodes=%d nf=%s\n" % (label, nodes, nfpp))
        fh.write("block_bytes=%d\n" % len(block))
        fh.write("mm1_bytes=%d\n" % len(src))
        fh.write("mm0rs_rc=%d\n" % r.returncode)
        fh.write("mm0c_rc=%d\n" % cc_rc)
        fh.write("mmb_bytes=%d\n" % mmb_bytes)
        fh.write("faithful=True\n")

    open("/tmp/bool_bridge.log", "w").write("\n".join(log) + "\n")
    print("done; rs_rc=%d cc_rc=%d" % (r.returncode, cc_rc))


if __name__ == "__main__":
    main()
