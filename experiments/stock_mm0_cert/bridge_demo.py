"""End-to-end spike: take a REAL src/expr.py kernel term, bridge it to the
db_cert de-Bruijn AST, certify its reduction, and check with stock mm0-c.

This is the first genuine kernel-integration data point: a term built from the
actual prelude's `Nat.rec` (not a hand-built db_cert demo), normalised by the
emitter and verified by the 815-line C kernel.

Faithfulness guard: we cross-check the db_cert normal form against the real
src/kernel.py whnf-normalisation of the SAME term, so a bridge mistranslation
can't slip through.
"""
import os, sys, subprocess

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
for p in (HERE, ROOT):
    if p not in sys.path:
        sys.path.insert(0, p)

from src import expr as E
from src.levels import LZero, LSucc
from src.env import Env
from src.kernel import Kernel, LocalCtx
from src.prelude_decls import build_stdlib

import bridge
import db_cert

MM0   = "/home/bepis/prog/scientific-computing/mm0"
MM0RS = f"{MM0}/mm0-rs/target/release/mm0-rs"
MM0C  = f"{MM0}/mm0-c/mm0-c-np"

Nat   = E.Const("Nat", ())
Zero  = E.Const("Nat.zero", ())
Succ  = lambda x: E.App(E.Const("Nat.succ", ()), x)
NatRec = lambda *lvls: E.Const("Nat.rec", tuple(lvls))   # one motive level

def numeral(n):
    t = Zero
    for _ in range(n):
        t = Succ(t)
    return t


def kernel_nf(K, e, ctx=None):
    """Full normal form via the real kernel's whnf (recurse into subterms)."""
    ctx = ctx or LocalCtx()
    e = K.whnf(e, ctx)
    if isinstance(e, E.App):
        return E.App(kernel_nf(K, e.fn, ctx), kernel_nf(K, e.arg, ctx))
    if isinstance(e, E.Lam):
        return E.Lam(e.binder, kernel_nf(K, e.dom, ctx), e.body)
    return e


def main():
    env = Env()
    build_stdlib(env)
    K = Kernel(env)

    # Build  add m n := Nat.rec (motive := \_:Nat. Nat) m (\k ih. succ ih) n
    # specialised to add 2 2.  Motive is non-dependent (\_:Nat. Nat).
    motive = E.Lam("_", Nat, Nat)                       # \_:Nat. Nat
    z_case = numeral(2)                                 # add 2 0 = 2
    s_case = E.Lam("k", Nat, E.Lam("ih", Nat, Succ(E.BVar(0))))  # \k ih. succ ih
    # Nat.rec has a single motive level param; motive : Nat -> Sort 0 (Type 0
    # is Sort 1, but the kernel infers; we pass level 1 to match Type0=Sort 1).
    term = E.app_many(NatRec(LSucc(LZero())), motive, z_case, s_case, numeral(2))

    # --- oracle: what does the REAL kernel say this reduces to? ---
    knf = kernel_nf(K, term)
    print("kernel normal form:", E.show(knf))
    assert knf == numeral(4), f"kernel says {E.show(knf)}, expected 4"

    # --- bridge to db_cert and certify the reduction ---
    dterm = bridge.to_db(term)
    nf, conv = db_cert.prove_norm(dterm)
    conv = conv or "(deq_refl)"
    bridged_nf = db_cert.pp(nf)
    expected_nf = db_cert.pp(bridge.to_db(numeral(4)))
    print("bridge normal form:", bridged_nf)
    assert bridged_nf == expected_nf, f"bridge nf {bridged_nf} != {expected_nf}"
    print("faithfulness: kernel nf and bridge nf agree (both = 4)  ✓")

    nodes = db_cert.proof_nodes(conv)
    thm = f"theorem bridge_add22: $ deq cnil {db_cert.pp(dterm)} {bridged_nf} $ =\n'{conv};\n"

    # db.mm1 has Nat hard-wired (tnat/tzero/tsucc/trec) -- no generated block needed
    prelude = open(f"{HERE}/db.mm1").read()
    open("/tmp/cert_bridge.mm1", "w").write(prelude + "\n" + thm)

    print(f"\nreal kernel term -> certificate: {nodes} proof nodes")
    print("=" * 60)
    r = subprocess.run([MM0RS, "compile", "/tmp/cert_bridge.mm1",
                        "/tmp/cert_bridge.mmb"], capture_output=True, text=True)
    print("mm0-rs verify:", "OK (exit 0)" if r.returncode == 0 else "FAIL")
    if r.returncode != 0:
        print(r.stdout[-3000:]); print(r.stderr[-3000:]); return
    sz = os.path.getsize("/tmp/cert_bridge.mmb")
    rc = subprocess.run([MM0C, "/tmp/cert_bridge.mmb"]).returncode
    print("mm0-c  verify:", "OK (exit 0)" if rc == 0 else f"FAIL ({rc})")
    print(f"certificate size: {sz} bytes")

    # structured result file (the stdout channel has been unreliable this session)
    with open("/tmp/bridge_result.txt", "w") as fh:
        fh.write("kernel_nf=%s\n" % E.show(knf))
        fh.write("bridge_nf=%s\n" % bridged_nf)
        fh.write("faithful=%s\n" % (bridged_nf == expected_nf))
        fh.write("nodes=%d\n" % nodes)
        fh.write("mm0rs_rc=%d\n" % r.returncode)
        fh.write("mm0c_rc=%d\n" % rc)
        fh.write("mmb_bytes=%d\n" % sz)


if __name__ == "__main__":
    main()
