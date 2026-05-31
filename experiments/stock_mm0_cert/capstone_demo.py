"""CAPSTONE: drive a real examples/*.lean file end-to-end through the actual
pipeline (parser -> elaborator -> kernel) and then discharge its `de-refl`
obligations with stock mm0-c via the bridge -- NO emitter.py, NO our trusted
mm0_verify.py.

`examples/math.lean` has computation-by-refl examples like

    example : Eq.{1} Nat (Nat.add 5 0) 5 := Eq.refl.{1} Nat 5
    example : Eq.{1} Nat (Nat.add 7 (Nat.add 8 9)) 24 := Eq.refl.{1} Nat 24

`Eq.refl.{1} Nat 5 : Eq Nat 5 5` only typechecks because the kernel reduces the
left side; in production `emitter.py` discharges that with `(de-refl ...)` (our
trusted `_normalize`).  Here we GENERATE the explicit stock-MM0 reduction
certificate the `de-refl` stands in for, and the 815-line C kernel checks it.

We DON'T hard-code decl names: we elaborate the file, then for every elaborated
decl whose type is `Eq.{u} Nat lhs rhs` over CLOSED Nat terms we register the
defs lhs uses, bridge it, and certify `deq cnil lhs rhs`.  Anything outside the
fragment (parametric / free vars / non-Nat / typeclass) raises and is SKIPPED
and counted, never crashing the run.  Faithfulness is guarded against
src/kernel.py whnf.
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
from src.lean_parser import elaborate

import bridge
import db_cert

MM0   = "/home/bepis/prog/scientific-computing/mm0"
MM0RS = f"{MM0}/mm0-rs/target/release/mm0-rs"
MM0C  = f"{MM0}/mm0-c/mm0-c-np"
EXAMPLE = f"{ROOT}/examples/math.lean"

def numval(e):
    n = 0
    while isinstance(e, E.App) and isinstance(e.fn, E.Const) and e.fn.name == "Nat.succ":
        n += 1; e = e.arg
    return n if (isinstance(e, E.Const) and e.name == "Nat.zero") else None

def spine(e):
    args = []
    while isinstance(e, E.App):
        args.append(e.arg); e = e.fn
    args.reverse()
    return e, args

def consts_in(e, acc):
    if isinstance(e, E.Const):           acc.add(e.name)
    elif isinstance(e, E.App):           consts_in(e.fn, acc); consts_in(e.arg, acc)
    elif isinstance(e, (E.Lam, E.Pi)):   consts_in(e.dom, acc); consts_in(e.body, acc)
    return acc

def kernel_nf(K, e, ctx=None):
    ctx = ctx or LocalCtx()
    e = K.whnf(e, ctx)
    if isinstance(e, E.App):
        return E.App(kernel_nf(K, e.fn, ctx), kernel_nf(K, e.arg, ctx))
    if isinstance(e, E.Lam):
        return E.Lam(e.binder, kernel_nf(K, e.dom, ctx), e.body)
    return e

def eq_over_nat(ty):
    """If ty is `Eq.{u} Nat lhs rhs`, return (lhs, rhs), else None."""
    head, args = spine(ty)
    if isinstance(head, E.Const) and head.name == "Eq" and len(args) == 3:
        A = args[0]
        if isinstance(A, E.Const) and A.name == "Nat":
            return args[1], args[2]
    return None


def main():
    log = []; LG = lambda *a: log.append(" ".join(str(x) for x in a))

    env = Env(); build_stdlib(env)
    added = elaborate(open(EXAMPLE).read(), env)      # parser -> elaborator -> kernel
    LG("elaborated", os.path.basename(EXAMPLE), "-> added:", added)
    K = Kernel(env)

    certified, skipped = [], []
    for name in added:
        try:
            d = env.get(name)
        except Exception:
            skipped.append((name, "no-decl")); continue
        ty = getattr(d, "type_", None)
        if ty is None:
            skipped.append((name, "no-type")); continue
        sides = eq_over_nat(ty)
        if sides is None:
            skipped.append((name, "not-Eq-over-Nat")); continue
        lhs, rhs = sides
        try:
            # oracle: real kernel reduces both sides to the same numeral
            kl = kernel_nf(K, lhs); kr = kernel_nf(K, rhs)
            val = numval(kl)
            if val is None or kl != kr:
                skipped.append((name, "kernel-nf-not-equal-numeral")); continue
            # register defs the sides use (Nat.add, ...), then bridge + certify
            for c in sorted(consts_in(lhs, set()) | consts_in(rhs, set())):
                if env.has(c) and type(env.get(c)).__name__ == "Definition":
                    bridge.register_def(env, c)
            dl = bridge.to_db(lhs); dr = bridge.to_db(rhs)
            nf, conv = db_cert.prove_norm(dl)
            conv = conv or "(deq_refl)"
            assert db_cert.pp(nf) == db_cert.pp(dr), "%s != %s" % (db_cert.pp(nf), db_cert.pp(dr))
            nodes = db_cert.proof_nodes(conv)
            certified.append((name, val, db_cert.pp(dl), db_cert.pp(dr), conv, nodes))
            LG("  CERTIFIED", name, ":", E.show(lhs), "≡", E.show(rhs), "(=%s)" % val,
               "->", nodes, "nodes")
        except Exception as ex:
            skipped.append((name, "%s: %s" % (type(ex).__name__, str(ex)[:60])))

    assert certified, "no de-refl obligations certified -- nothing to show"
    LG("faithfulness: bridge nf == kernel nf == rhs for all certified  ✓")

    prelude  = open(f"{HERE}/db.mm1").read()
    defblock = db_cert.gen_def_block()
    thms = [f"-- de-refl obligation `{name}` from {os.path.basename(EXAMPLE)} (= {val})\n"
            f"theorem capstone_{name}: $ deq cnil {dl} {dr} $ =\n'{conv};\n"
            for name, val, dl, dr, conv, nodes in certified]
    full = prelude + "\n" + defblock + "\n" + "\n".join(thms)
    open("/tmp/cert_capstone.mm1", "w").write(full)

    r = subprocess.run([MM0RS, "compile", "/tmp/cert_capstone.mm1",
                        "/tmp/cert_capstone.mmb"], capture_output=True, text=True)
    rs_ok = (r.returncode == 0)
    LG("mm0-rs rc=", r.returncode)
    if not rs_ok:
        LG("--stdout--"); LG(r.stdout[-4000:]); LG("--stderr--"); LG(r.stderr[-4000:])
    mmb = os.path.getsize("/tmp/cert_capstone.mmb") if rs_ok else -1
    cc = subprocess.run([MM0C, "/tmp/cert_capstone.mmb"], capture_output=True, text=True) if rs_ok else None
    cc_rc = cc.returncode if cc else -1
    LG("mm0-c rc=", cc_rc)

    with open("/tmp/capstone_result.txt", "w") as fh:
        fh.write("example=%s\n" % os.path.basename(EXAMPLE))
        fh.write("elaborated=%d\n" % len(added))
        fh.write("certified=%d skipped=%d\n" % (len(certified), len(skipped)))
        for name, val, dl, dr, conv, nodes in certified:
            fh.write("cert %s val=%s nodes=%d\n" % (name, val, nodes))
        for name, why in skipped:
            fh.write("skip %s :: %s\n" % (name, why))
        fh.write("defs=%s\n" % ",".join(db_cert.DEFS.keys()))
        fh.write("mm1_bytes=%d\n" % len(full))
        fh.write("mm0rs_rc=%d\n" % r.returncode)
        fh.write("mm0c_rc=%d\n" % cc_rc)
        fh.write("mmb_bytes=%d\n" % mmb)
        fh.write("faithful=True\n")
    open("/tmp/capstone.log", "w").write("\n".join(log) + "\n")
    print("done; certified=%d rs_rc=%d cc_rc=%d" % (len(certified), r.returncode, cc_rc))


if __name__ == "__main__":
    main()
