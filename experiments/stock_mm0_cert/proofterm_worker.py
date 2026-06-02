"""Proof-TERM worker: certify ONE decl's whole proof term through stock MM0 by
TYPING it -- ht cnil <body> <stated-type> -- instead of the de-refl conversion the
coverage worker does.  This reaches proofs that USE the induction hypothesis / case
analysis / a transport (Eq.rec), not just rfl leaves.

Run as a subprocess (fresh bridge/db_cert globals per decl).  Usage:
  python3 proofterm_worker.py <file.lean> <decl-name>

Scope: a closed, MONOMORPHIC proof whose body bridges within the supported fragment
(Nat / Bool / List / Eq / Vec + delta-inlined defs).  A poly proof (`.{u}`) whose
body drives a recursor at a generic motive level still needs open-level normalisation
and is out of scope here.  Prints one RESULT line.
"""
import os, re, sys, subprocess

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
for p in (HERE, ROOT):
    if p not in sys.path:
        sys.path.insert(0, p)

from src import expr as E
from src.env import Env
from src.prelude_decls import build_stdlib
from src.lean_parser import elaborate
import bridge, db_cert, induct
from induct import Inductive, Ctor

MM0   = "/home/bepis/prog/scientific-computing/mm0"
MM0RS = f"{MM0}/mm0-rs/target/release/mm0-rs"
MM0C  = f"{MM0}/mm0-c/mm0-c-np"
BOOL_P = Inductive("tbool", "(lS lz)", [Ctor("bfalse", ()), Ctor("btrue", ())], "brec")


def consts_in(e, acc):
    if isinstance(e, E.Const):           acc.add(e.name)
    elif isinstance(e, E.App):           consts_in(e.fn, acc); consts_in(e.arg, acc)
    elif isinstance(e, (E.Lam, E.Pi)):   consts_in(e.dom, acc); consts_in(e.body, acc)
    elif isinstance(e, E.Let):           consts_in(e.type_, acc); consts_in(e.value, acc); consts_in(e.body, acc)
    return acc


def main():
    fname, decl = sys.argv[1], sys.argv[2]
    base = os.path.basename(fname)

    def fail(tag):
        print(f"RESULT {base}:{decl} status={tag} nodes=0 rs_rc=-3 cc_rc=-3")

    try:
        env = Env(); build_stdlib(env)
        blocks = (induct.generate(BOOL_P) + "\n" + induct.generate(induct.LIST) + "\n"
                  + induct.generate(induct.EQ) + "\n" + induct.generate(induct.VEC) + "\n")
        elaborate(open(fname).read(), env)
        bridge.bind_env(env)
        d = env.get(decl)
    except Exception as ex:
        return fail("elab:%s" % type(ex).__name__)

    try:
        for c in sorted(consts_in(d.value, set()) | consts_in(d.type_, set())):
            if c != decl and env.has(c) and type(env.get(c)).__name__ == "Definition" \
               and not env.get(c).level_params:
                bridge.register_def(env, c)
        dty = bridge.to_db(d.type_)
        dbody = bridge.to_db(d.value)
        tb, pb = db_cert.prove_ht(dbody, [])          # type the proof term
        proof = db_cert._coerce(pb, tb, dty, [])      # coerce inferred -> stated type
        nodes = db_cert.proof_nodes(proof)
        bodys, tys = db_cert.pp(dbody), db_cert.pp(dty)
    except Exception as ex:
        return fail("%s:%s" % (type(ex).__name__, str(ex).split(chr(10))[0][:30].replace(" ", "_")))

    # universe params -> (lv_u: lvl) theorem binders, so a LEVEL-POLYMORPHIC proof
    # (e.g. my_eq_symm.{u}) is certified generically -- the poly Eq axioms unify the
    # level at each use site, exactly as for level-generic de-refl obligations.
    lps = [bridge.level_param_name(p) for p in (getattr(d, "level_params", ()) or ())]
    blob = bodys + tys + proof
    binders = "".join(f" ({p}: lvl)" for p in lps
                      if re.search(r"\b" + re.escape(p) + r"\b", blob))

    prelude  = open(f"{HERE}/db.mm1").read()
    decls_block = db_cert.gen_all_blocks()     # defs + opaque lemmas + axioms, dep-ordered
    ind_blocks = "".join(bridge.IND_EMITTED)
    thm = f"theorem pt{binders}: $ ht cnil {bodys} {tys} $ =\n'{proof};\n"
    full = (prelude + "\n" + blocks + "\n" + ind_blocks + "\n" + decls_block + "\n" + thm)
    mm1 = f"/tmp/pt_{base}_{decl}.mm1"; mmb = f"/tmp/pt_{base}_{decl}.mmb"
    open(mm1, "w").write(full)

    r = subprocess.run([MM0RS, "compile", mm1, mmb], capture_output=True, text=True)
    rs_rc = r.returncode
    if rs_rc != 0:
        open(mm1 + ".err", "w").write(r.stdout[-3000:] + "\n" + r.stderr[-3000:])
        cc_rc = -1
    else:
        cc_rc = subprocess.run([MM0C, mmb], capture_output=True).returncode
    status = "certified" if (rs_rc == 0 and cc_rc == 0) else "checker-FAIL"
    print(f"RESULT {base}:{decl} status={status} nodes={nodes} rs_rc={rs_rc} cc_rc={cc_rc}")


if __name__ == "__main__":
    main()
