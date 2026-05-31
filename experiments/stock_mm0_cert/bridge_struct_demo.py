"""Structure/class bridging demo: drive examples/arith.lean through the real
pipeline and certify its `Eq Nat ... ` de-refl obligations (four_eq, twelve_eq,
sixteen_eq) -- which go through a typeclass projection `Add.add` and an instance
`addNat = Add.mk Nat Nat.add` -- against stock mm0-rs AND mm0-c.  This exercises
bridge.register_inductive (auto-deriving the db.mm1 block for the `Add`/`Mul`
classes from the kernel) plus the existing delta path for the projection+instance.

Usage: python3 bridge_struct_demo.py [examples/file.lean]
"""
import os, sys, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
for p in (HERE, ROOT):
    if p not in sys.path: sys.path.insert(0, p)
from src import expr as E
from src.env import Env
from src.kernel import Kernel, LocalCtx
from src.prelude_decls import build_stdlib
from src.lean_parser import elaborate
import bridge, db_cert, induct
from induct import Inductive, Ctor

MM0 = "/home/bepis/prog/scientific-computing/mm0"
MM0RS = f"{MM0}/mm0-rs/target/release/mm0-rs"
MM0C = f"{MM0}/mm0-c/mm0-c-np"
BOOL_P = Inductive("tbool", "(lS lz)", [Ctor("bfalse", ()), Ctor("btrue", ())], "brec")

def spine(e):
    a = []
    while isinstance(e, E.App): a.append(e.arg); e = e.fn
    a.reverse(); return e, a
def eq_obl(ty):
    h, ar = spine(ty)
    if isinstance(h, E.Const) and h.name == "Eq" and len(ar) == 3:
        return ar[0], ar[1], ar[2]
    return None
def consts_in(e, acc):
    if isinstance(e, E.Const): acc.add(e.name)
    elif isinstance(e, E.App): consts_in(e.fn, acc); consts_in(e.arg, acc)
    elif isinstance(e, (E.Lam, E.Pi)): consts_in(e.dom, acc); consts_in(e.body, acc)
    return acc

fname = sys.argv[1] if len(sys.argv) > 1 else ROOT + "/examples/arith.lean"
env = Env(); build_stdlib(env)
blocks = (induct.generate(BOOL_P) + "\n" + induct.generate(induct.LIST) + "\n"
          + induct.generate(induct.EQ) + "\n" + induct.generate(induct.VEC) + "\n")
added = elaborate(open(fname).read(), env)
K = Kernel(env)

def knf(e, ctx=None):
    ctx = ctx or LocalCtx(); e = K.whnf(e, ctx)
    if isinstance(e, E.App): return E.App(knf(e.fn, ctx), knf(e.arg, ctx))
    if isinstance(e, E.Lam): return E.Lam(e.binder, knf(e.dom, ctx), e.body)
    return e

certs = []
for name in added:
    try: d = env.get(name)
    except Exception: continue
    ty = getattr(d, "type_", None)
    sides = eq_obl(ty) if ty is not None else None
    if sides is None: continue
    A, lhs, rhs = sides
    try:
        if knf(lhs) != knf(rhs):
            print("  SKIP %s: not convertible at kernel" % name); continue
        for c in sorted(consts_in(lhs, set()) | consts_in(rhs, set())):
            if env.has(c) and type(env.get(c)).__name__ == "Definition" \
               and not env.get(c).level_params:
                bridge.register_def(env, c)
        dl = bridge.to_db(lhs); dr = bridge.to_db(rhs)
        conv = db_cert.prove_conv(dl, dr) or "(deq_refl)"
        nfa, _ = db_cert.prove_norm(dl); nfb, _ = db_cert.prove_norm(dr)
        assert db_cert.pp(nfa) == db_cert.pp(nfb), "bridge nf mismatch"
        certs.append((name, conv, db_cert.proof_nodes(conv)))
        print("  CERT %s  (%d proof nodes)" % (name, db_cert.proof_nodes(conv)))
    except Exception as ex:
        import traceback; print("  FAIL %s: %s" % (name, ex))
        traceback.print_exc()

print("\ninductive blocks auto-generated:", len(bridge.IND_EMITTED))
if not certs:
    print("no obligations certified; nothing to check"); print("SENTINEL_DEMO"); sys.exit(0)

prelude = open(f"{HERE}/db.mm1").read()
defblock = db_cert.gen_def_block()
# build the theorems by re-deriving each obligation's bridged sides + conv proof
real_thms = []
for i, name in enumerate([c[0] for c in certs]):
    d = env.get(name); A, lhs, rhs = eq_obl(d.type_)
    dl = bridge.to_db(lhs); dr = bridge.to_db(rhs)
    conv = db_cert.prove_conv(dl, dr) or "(deq_refl)"
    real_thms.append(f"theorem sd_{i}:\n  $ deq cnil {db_cert.pp(dl)} {db_cert.pp(dr)} $ =\n'{conv};\n")

full = (prelude + "\n" + blocks + "\n" + "".join(bridge.IND_EMITTED) + "\n"
        + defblock + "\n" + "\n".join(real_thms))
mm1 = "/tmp/struct_demo.mm1"; mmb = "/tmp/struct_demo.mmb"
open(mm1, "w").write(full)
r = subprocess.run([MM0RS, "compile", mm1, mmb], capture_output=True, text=True)
print("mm0-rs rc =", r.returncode)
if r.returncode != 0:
    open("/tmp/struct_demo.err", "w").write(r.stdout[-4000:] + "\n---\n" + r.stderr[-4000:])
    print("  (stderr tail saved to /tmp/struct_demo.err)")
else:
    cc = subprocess.run([MM0C, mmb], capture_output=True, text=True)
    print("mm0-c  rc =", cc.returncode)
print("SENTINEL_DEMO")
