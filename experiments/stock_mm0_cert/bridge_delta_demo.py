"""δ (definitional unfolding): bridge REAL prelude *definitions* through stock
mm0-c.  Takes terms built from the prelude's `Nat.add` / `Nat.pred` (which are
`def`s, not primitives), bridges them, certifies the δ+β+ι reduction, and checks
with stock mm0-rs + mm0-c.

The faithful trick (validated separately): a CIC `def d := body` becomes a
stock-MM0 `def d: expr = $ body $;`, so δ-unfolding is mm0's OWN native
def-unfold -- it adds NO trusted axiom.  In the certificate, the δ step is even
free: the proof is generated about `body @ args`, and mm0 accepts it for the
`d @ args` theorem because `d ≡ body` definitionally.  So db_cert.whnf just
swaps a def head for its body and keeps reducing.

`Nat.add = λ m n. Nat.rec (λ_.Nat) m (λ k ih. succ ih) n` and `Nat.pred` use
only Nat primitives, so once δ-unfolded the existing β+ι machinery finishes.

Faithfulness guard: db_cert normal form is cross-checked against src/kernel.py
whnf (which does its own δ) of the same term before certifying.
"""
import os, sys, subprocess

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
for p in (HERE, ROOT):
    if p not in sys.path:
        sys.path.insert(0, p)

from src import expr as E
from src.env import Env
from src.kernel import Kernel, LocalCtx
from src.prelude_decls import build_stdlib

import bridge
import db_cert

MM0   = "/home/bepis/prog/scientific-computing/mm0"
MM0RS = f"{MM0}/mm0-rs/target/release/mm0-rs"
MM0C  = f"{MM0}/mm0-c/mm0-c-np"

Zero = E.Const("Nat.zero", ())
Succ = lambda x: E.App(E.Const("Nat.succ", ()), x)
Add  = lambda a, b: E.app_many(E.Const("Nat.add", ()), a, b)
Pred = lambda a: E.app_many(E.Const("Nat.pred", ()), a)

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

    # register the prelude defs for δ (maps Nat.add -> Nat_add, body into DEFS)
    bridge.register_def(env, "Nat.add")
    bridge.register_def(env, "Nat.pred")

    cases = [
        ("add_2_3", Add(numeral(2), numeral(3)), 5),
        ("add_0_4", Add(numeral(0), numeral(4)), 4),
        ("pred_3",  Pred(numeral(3)),            2),
        ("pred_0",  Pred(numeral(0)),            0),
    ]
    results = []
    for label, term, expected in cases:
        knf = kernel_nf(K, term)
        LG(label, "kernel_nf=", E.show(knf))
        assert numval(knf) == expected, f"{label}: kernel says {E.show(knf)}"

        dterm = bridge.to_db(term)
        nf, conv = db_cert.prove_norm(dterm)
        conv = conv or "(deq_refl)"
        bridged_nf = db_cert.pp(nf)
        expected_nf = db_cert.pp(bridge.to_db(numeral(expected)))
        LG("  bridge_nf=", bridged_nf, " expected=", expected_nf)
        assert bridged_nf == expected_nf, f"{label}: bridge nf {bridged_nf} != {expected_nf}"

        nodes = db_cert.proof_nodes(conv)
        results.append((label, db_cert.pp(dterm), bridged_nf, conv, nodes))

    # assemble: db.mm1 (core + Nat) then the `def` block (δ via mm0 native unfold)
    prelude  = open(f"{HERE}/db.mm1").read()
    defblock = db_cert.gen_def_block()
    thms = [f"theorem bridge_{label}: $ deq cnil {dpp} {nfpp} $ =\n'{conv};\n"
            for label, dpp, nfpp, conv, nodes in results]
    src = prelude + "\n" + defblock + "\n" + "\n".join(thms)
    open("/tmp/cert_delta.mm1", "w").write(src)
    LG("def block:\n" + defblock)

    r = subprocess.run([MM0RS, "compile", "/tmp/cert_delta.mm1",
                        "/tmp/cert_delta.mmb"], capture_output=True, text=True)
    rs_ok = (r.returncode == 0)
    LG("mm0-rs rc=", r.returncode)
    if not rs_ok:
        LG("---mm0-rs stdout---"); LG(r.stdout[-4000:])
        LG("---mm0-rs stderr---"); LG(r.stderr[-4000:])

    mmb_bytes = os.path.getsize("/tmp/cert_delta.mmb") if rs_ok else -1
    cc = subprocess.run([MM0C, "/tmp/cert_delta.mmb"], capture_output=True, text=True) \
         if rs_ok else None
    cc_rc = cc.returncode if cc else -1
    LG("mm0-c rc=", cc_rc)

    with open("/tmp/delta_bridge_result.txt", "w") as fh:
        fh.write("cases=%s\n" % ",".join(label for label, *_ in results))
        for label, dpp, nfpp, conv, nodes in results:
            fh.write("%s nodes=%d nf=%s\n" % (label, nodes, nfpp))
        fh.write("defs=%s\n" % ",".join(db_cert.DEFS.keys()))
        fh.write("defblock_bytes=%d\n" % len(defblock))
        fh.write("mm1_bytes=%d\n" % len(src))
        fh.write("mm0rs_rc=%d\n" % r.returncode)
        fh.write("mm0c_rc=%d\n" % cc_rc)
        fh.write("mmb_bytes=%d\n" % mmb_bytes)
        fh.write("faithful=True\n")

    open("/tmp/delta_bridge.log", "w").write("\n".join(log) + "\n")
    print("done; rs_rc=%d cc_rc=%d" % (r.returncode, cc_rc))


if __name__ == "__main__":
    main()
