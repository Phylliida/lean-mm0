"""Whole-ENVIRONMENT certification worker: type-check EVERY declaration in one
examples/*.lean against the 815-line stock base -- not just its `Eq` goals.

Where coverage_worker asks "do this file's de-refl / proof obligations certify?",
this asks the stronger question: "does the tiny stock base re-typecheck every
declaration our kernel elaborated?"  For each decl with a body, certify
`ht cnil <value> <type>` -- the kernel's OWN typing of the decl, re-derived as an
explicit stock-MM0 proof and checked by BOTH mm0-rs and the 815-line mm0-c.  This is
the strongest form of the experiment's thesis: the trusted base verifies the whole
environment, faithful by construction (the term and type are the kernel's own).

Axioms / inductives (no value) have nothing to type and are not counted.  Out-of-
fragment decls are caught per-decl and counted as skips with a precise reason.

Run as a subprocess (fresh bridge/db_cert globals per file).  Usage:
  python3 envcert_worker.py <file.lean>
Prints exactly one machine-readable line:
  RESULT <file> elaborated=<n> decls=<n> certified=<n> skipped=<n> \
         rs_rc=<n> cc_rc=<n> nodes=<csv> reasons=<csv>
"""
import os, sys, re, subprocess, traceback

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


def _reason(prefix, ex):
    m = re.search(r"'([^']+)'", str(ex))
    tok = m.group(1) if m else (str(ex).split(":")[0].split() or [""])[0]
    tok = re.sub(r"[^A-Za-z0-9_.]+", "_", tok)[:32].strip("_")
    return prefix + (":" + tok if tok else "")


def main():
    fname = sys.argv[1]
    base = os.path.basename(fname)

    try:
        env = Env(); build_stdlib(env)
        blocks = (induct.generate(BOOL_P) + "\n" + induct.generate(induct.LIST) + "\n"
                  + induct.generate(induct.EQ) + "\n" + induct.generate(induct.VEC) + "\n")
        added = elaborate(open(fname).read(), env)
        bridge.bind_env(env)
    except Exception as ex:
        open("/tmp/envfail_%s.txt" % base, "w").write(traceback.format_exc())
        print("RESULT %s elaborated=ERR decls=0 certified=0 skipped=0 rs_rc=-3 cc_rc=-3 "
              "nodes=- reasons=elab:%s" % (base, type(ex).__name__))
        return

    certified, skipped = [], []
    for name in added:
        try:
            d = env.get(name)
        except Exception:
            continue
        val = getattr(d, "value", None)
        ty  = getattr(d, "type_", None)
        if val is None or ty is None:
            continue                          # axiom / inductive: no body to type
        try:
            for c in sorted(consts_in(val, set()) | consts_in(ty, set())):
                if c != name and env.has(c) and type(env.get(c)).__name__ == "Definition" \
                   and not env.get(c).level_params:
                    bridge.register_def(env, c)
            dty   = bridge.to_db(ty)
            dbody = bridge.to_db(val)
            tb, pb = db_cert.prove_ht(dbody, [])      # the kernel's typing, re-derived
            proof  = db_cert._coerce(pb, tb, dty, [])
            bodys, tys = db_cert.pp(dbody), db_cert.pp(dty)
            lps = [bridge.level_param_name(p) for p in (getattr(d, "level_params", ()) or ())]
            blob = bodys + tys + proof
            binders = "".join(f" ({p}: lvl)" for p in lps
                              if re.search(r"\b" + re.escape(p) + r"\b", blob))
            certified.append({"name": name, "binders": binders, "body": bodys,
                              "type": tys, "proof": proof, "nodes": db_cert.proof_nodes(proof)})
        except bridge.Unsupported as ex:
            skipped.append(_reason("unsup", ex))
        except Exception as ex:
            skipped.append(_reason(type(ex).__name__, ex))

    decls = len(certified) + len(skipped)
    nodes_csv = ",".join(str(c["nodes"]) for c in certified)
    reasons_csv = ",".join(sorted(set(skipped)))

    rs_rc = cc_rc = -2
    if certified:
        prelude     = open(f"{HERE}/db.mm1").read()
        defblock    = db_cert.gen_def_block()
        opaqueblock = db_cert.gen_opaque_block()
        axiomblock  = db_cert.gen_axiom_block()   # source-level axioms, carried as assumptions
        ind_blocks  = "".join(bridge.IND_EMITTED)
        thms = [f"theorem env_{i}{c['binders']}: $ ht cnil {c['body']} {c['type']} $ =\n'{c['proof']};\n"
                for i, c in enumerate(certified)]
        # axioms' types reference inductives (-> after blocks/ind_blocks); defs/opaque
        # lemmas may cite an axiom (-> axiomblock before them).
        full = (prelude + "\n" + blocks + "\n" + ind_blocks + "\n" + axiomblock + "\n"
                + defblock + "\n" + opaqueblock + "\n" + "\n".join(thms))
        mm1 = f"/tmp/env_{base}.mm1"; mmb = f"/tmp/env_{base}.mmb"
        open(mm1, "w").write(full)
        r = subprocess.run([MM0RS, "compile", mm1, mmb], capture_output=True, text=True)
        rs_rc = r.returncode
        if rs_rc == 0:
            cc_rc = subprocess.run([MM0C, mmb], capture_output=True).returncode
        else:
            cc_rc = -1
            open(f"/tmp/env_{base}.err", "w").write(r.stdout[-3000:] + "\n" + r.stderr[-3000:])

    axioms_csv = ",".join(sorted(db_cert.AXIOMS)) if certified else "-"
    print("RESULT %s elaborated=%d decls=%d certified=%d skipped=%d rs_rc=%d cc_rc=%d "
          "nodes=%s reasons=%s axioms=%s" %
          (base, len(added), decls, len(certified), len(skipped),
           rs_rc, cc_rc, nodes_csv or "-", reasons_csv or "-", axioms_csv or "-"))


if __name__ == "__main__":
    try:
        main()
    except Exception:
        b = os.path.basename(sys.argv[1]) if len(sys.argv) > 1 else "?"
        print("RESULT %s elaborated=ERR decls=0 certified=0 skipped=0 rs_rc=-4 cc_rc=-4 "
              "nodes=- reasons=worker:crash" % b)
        sys.stderr.write(traceback.format_exc())
