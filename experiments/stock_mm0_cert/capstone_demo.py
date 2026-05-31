"""CAPSTONE: drive a real examples/*.lean file end-to-end through the actual
pipeline (parser -> elaborator -> kernel) and then discharge its `de-refl`
obligations with stock mm0-c via the bridge -- with NO emitter.py and NO our
trusted mm0_verify.py.

`examples/arith.lean` contains:

    theorem two_plus_three : Eq.{1} Nat (Nat.add 2 3) 5 := Eq.refl.{1} Nat 5
    -- our verifier normalizes both sides, so this typechecks
    theorem nine : Eq.{1} Nat (Nat.add (Nat.add 2 3) 4) 9 := Eq.refl.{1} Nat 9

`Eq.refl.{1} Nat 5 : Eq Nat 5 5` only checks against `Eq Nat (Nat.add 2 3) 5`
because the kernel reduces `Nat.add 2 3` to `5`.  In the production pipeline
`emitter.py` discharges that with `(de-refl ...)` -- our trusted `_normalize`
does the reduction.  Here we GENERATE the explicit stock-MM0 reduction
certificate (the thing `de-refl` stands in for) and the 815-line C kernel checks
it.  `nine` nests `Nat.add (Nat.add 2 3) 4` -- a def inside a def's argument,
exercising the δ shift/subst path.

For each target theorem we read its ELABORATED type out of the env, split the
`Eq` into (lhs, rhs), register the defs lhs uses (Nat.add), bridge lhs, and
certify `deq cnil lhs rhs`.  Faithfulness is guarded against src/kernel.py whnf.

(Scope: monomorphic, Nat-fragment de-refl obligations.  Universe-polymorphic
defs -- id_poly.{u} etc. in no_levels.lean -- need level-param tracking in the
bridge and remain a follow-up; here arith.lean's other decls elaborate but are
not the de-refl targets.)
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
EXAMPLE = f"{ROOT}/examples/arith.lean"
TARGETS = ["two_plus_three", "nine"]

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

def eq_sides(ty):
    """Eq.{u} A lhs rhs  ->  (lhs, rhs)."""
    head, args = spine(ty)
    assert isinstance(head, E.Const) and head.name == "Eq", f"not an Eq type: {E.show(ty)}"
    assert len(args) == 3, f"Eq arity {len(args)}"
    return args[1], args[2]

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


def main():
    log = []
    LG = lambda *a: log.append(" ".join(str(x) for x in a))

    # --- the REAL pipeline: parse + elaborate + kernel-check the .lean file ---
    env = Env(); build_stdlib(env)
    added = elaborate(open(EXAMPLE).read(), env)     # parser -> elaborator -> kernel
    LG("elaborated", os.path.basename(EXAMPLE), "-> %d decls" % len(added))
    K = Kernel(env)

    results = []
    for name in TARGETS:
        assert env.has(name), f"{name} not elaborated"
        thm = env.get(name)
        lhs, rhs = eq_sides(thm.type_)               # the de-refl obligation: lhs ≡ rhs
        LG(name, ":", E.show(lhs), "≡", E.show(rhs))

        # register the defs the lhs uses (Nat.add, recursively), then bridge
        for c in sorted(consts_in(lhs, set())):
            if env.has(c) and type(env.get(c)).__name__ == "Definition":
                bridge.register_def(env, c)

        # oracle: the real kernel reduces both sides to the same nf
        knf_l = kernel_nf(K, lhs); knf_r = kernel_nf(K, rhs)
        assert knf_l == knf_r, f"{name}: kernel {E.show(knf_l)} != {E.show(knf_r)}"
        LG("  kernel: both sides ->", E.show(knf_l), "=", numval(knf_l))

        dl = bridge.to_db(lhs); dr = bridge.to_db(rhs)
        nf, conv = db_cert.prove_norm(dl)
        conv = conv or "(deq_refl)"
        assert db_cert.pp(nf) == db_cert.pp(dr), f"{name}: {db_cert.pp(nf)} != {db_cert.pp(dr)}"
        nodes = db_cert.proof_nodes(conv)
        results.append((name, db_cert.pp(dl), db_cert.pp(dr), conv, nodes, numval(knf_l)))

    LG("faithfulness: bridge nf == kernel nf == rhs for all targets  ✓")

    prelude  = open(f"{HERE}/db.mm1").read()
    defblock = db_cert.gen_def_block()
    thms = [f"-- de-refl obligation of `{name}` in arith.lean  ({val})\n"
            f"theorem capstone_{name}: $ deq cnil {dl} {dr} $ =\n'{conv};\n"
            for name, dl, dr, conv, nodes, val in results]
    full = prelude + "\n" + defblock + "\n" + "\n".join(thms)
    open("/tmp/cert_capstone.mm1", "w").write(full)
    LG("defs registered:", list(db_cert.DEFS.keys()))

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
        fh.write("elaborated_decls=%d\n" % len(added))
        for name, dl, dr, conv, nodes, val in results:
            fh.write("%s obligation=>%s nodes=%d\n" % (name, val, nodes))
        fh.write("defs=%s\n" % ",".join(db_cert.DEFS.keys()))
        fh.write("mm1_bytes=%d\n" % len(full))
        fh.write("mm0rs_rc=%d\n" % r.returncode)
        fh.write("mm0c_rc=%d\n" % cc_rc)
        fh.write("mmb_bytes=%d\n" % mmb)
        fh.write("faithful=True\n")

    open("/tmp/capstone.log", "w").write("\n".join(log) + "\n")
    print("done; rs_rc=%d cc_rc=%d" % (r.returncode, cc_rc))


if __name__ == "__main__":
    main()
