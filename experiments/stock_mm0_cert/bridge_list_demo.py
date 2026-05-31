"""Widen the kernel-integration bridge past Nat: take a REAL src/expr.py term
built from the prelude's *parametric* `List.rec`, bridge it to db_cert, certify
the reduction, and check with stock mm0-rs + mm0-c.

This is the second kernel-integration data point (the first, bridge_demo.py,
was the closed Nat fragment).  List is the natural step past Nat: it is
parametric (one type parameter A) and has a genuine `Recursor` decl in the real
prelude -- unlike Bool, whose elimination is only a `casesOn` Definition that
would need delta-unfolding.

The List axiom block is *generated* by induct.generate(LIST) (the same
generator the run_induct.py demos use), appended after db.mm1's core+Nat.

Faithfulness guard: the db_cert normal form is cross-checked against the real
src/kernel.py whnf-normalisation of the SAME term, so a bridge mistranslation
cannot slip through.
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

# --- real prelude term builders (List Nat) ---
Z    = LZero()
Nat  = E.Const("Nat", ())
Zero = E.Const("Nat.zero", ())
Succ = lambda x: E.App(E.Const("Nat.succ", ()), x)

def numeral(n):
    t = Zero
    for _ in range(n):
        t = Succ(t)
    return t

Nil  = E.App(E.Const("List.nil", (Z,)), Nat)                     # List.nil.{0} Nat
Cons = lambda h, t: E.app_many(E.Const("List.cons", (Z,)), Nat, h, t)
ListNat = E.App(E.Const("List", (Z,)), Nat)

def listof(*xs):
    t = Nil
    for x in reversed(xs):
        t = Cons(x, t)
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


def build_length(xs):
    """length-as-List.rec applied to the list [xs...] : List Nat, -> Nat."""
    motive  = E.Lam("_", ListNat, Nat)                          # \_. Nat
    nil_case = Zero                                             # length nil = 0
    # \hd tl ih. succ ih
    cons_case = E.Lam("hd", Nat, E.Lam("tl", ListNat,
                       E.Lam("ih", Nat, Succ(E.BVar(0)))))
    rec = E.Const("List.rec", (Z,))                            # one level param
    return E.app_many(rec, Nat, motive, nil_case, cons_case, listof(*xs))


def main():
    log = []
    LG = lambda *a: log.append(" ".join(str(x) for x in a))

    env = Env(); build_stdlib(env)
    K = Kernel(env)

    # generate + register the List block with db_cert (must precede prove_norm)
    block = induct.generate(induct.LIST)

    cases = [([Zero], 1), ([Zero, Zero], 2), ([Zero, Zero, Zero], 3)]
    results = []
    for xs, expected in cases:
        term = build_length(xs)

        # oracle: real kernel
        knf = kernel_nf(K, term)
        kval = E.show(knf)
        LG("case len", len(xs), "kernel_nf=", kval)
        assert knf == numeral(expected), f"kernel says {kval}, expected {expected}"

        # bridge + certify
        dterm = bridge.to_db(term)
        nf, conv = db_cert.prove_norm(dterm)
        conv = conv or "(deq_refl)"
        bridged_nf = db_cert.pp(nf)
        expected_nf = db_cert.pp(bridge.to_db(numeral(expected)))
        LG("  bridge_nf=", bridged_nf, " expected=", expected_nf)
        assert bridged_nf == expected_nf, f"bridge nf {bridged_nf} != {expected_nf}"

        nodes = db_cert.proof_nodes(conv)
        results.append((len(xs), expected, db_cert.pp(dterm), bridged_nf, conv, nodes))

    # build one .mm1 with all theorems
    prelude = open(f"{HERE}/db.mm1").read()
    thms = []
    for i, (n, expected, dpp, nfpp, conv, nodes) in enumerate(results):
        thms.append(f"theorem bridge_len_{n}: $ deq cnil {dpp} {nfpp} $ =\n'{conv};\n")
    src = prelude + "\n" + block + "\n" + "\n".join(thms)
    open("/tmp/cert_list.mm1", "w").write(src)
    LG("wrote /tmp/cert_list.mm1", len(src), "bytes")

    # verify
    r = subprocess.run([MM0RS, "compile", "/tmp/cert_list.mm1",
                        "/tmp/cert_list.mmb"], capture_output=True, text=True)
    rs_ok = (r.returncode == 0)
    LG("mm0-rs rc=", r.returncode)
    if not rs_ok:
        LG("---mm0-rs stdout---"); LG(r.stdout[-4000:])
        LG("---mm0-rs stderr---"); LG(r.stderr[-4000:])

    mmb_bytes = os.path.getsize("/tmp/cert_list.mmb") if rs_ok else -1
    cc = subprocess.run([MM0C, "/tmp/cert_list.mmb"], capture_output=True, text=True) \
         if rs_ok else None
    cc_rc = cc.returncode if cc else -1
    LG("mm0-c rc=", cc_rc)

    # compact result file
    with open("/tmp/list_bridge_result.txt", "w") as fh:
        fh.write("cases=%s\n" % ",".join("len%d=>%d" % (n, e)
                                         for n, e, *_ in results))
        for n, e, dpp, nfpp, conv, nodes in results:
            fh.write("len%d nodes=%d nf=%s\n" % (n, nodes, nfpp))
        fh.write("block_bytes=%d\n" % len(block))
        fh.write("mm1_bytes=%d\n" % len(src))
        fh.write("mm0rs_rc=%d\n" % r.returncode)
        fh.write("mm0c_rc=%d\n" % cc_rc)
        fh.write("mmb_bytes=%d\n" % mmb_bytes)
        fh.write("faithful=True\n")  # asserts above guarantee it if we got here

    open("/tmp/list_bridge.log", "w").write("\n".join(log) + "\n")
    print("done; rs_rc=%d cc_rc=%d" % (r.returncode, cc_rc))


if __name__ == "__main__":
    main()
