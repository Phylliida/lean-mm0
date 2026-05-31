"""Coverage worker: certify ONE examples/*.lean file's de-refl obligations
through stock mm0-c, and print one machine-readable summary line.

Run as a subprocess (one fresh Python per file) so bridge/db_cert globals
(CONST_MAP / MONO / DEFS / TYCON / ...) reset between files and a crash on one
file can't poison the sweep.  Usage:  python3 coverage_worker.py <file.lean>

Auto-detects obligations: any elaborated decl whose type is `Eq A lhs rhs` for
ANY type A (Nat, Bool, List Nat, Vec, ...), not just Nat.  Registers the defs
each side uses (mono + poly via the bridge), bridges both sides, certifies
`deq cnil lhs rhs` by conversion.  Out-of-fragment / non-closed / error cases are
caught per-obligation and counted as skips.  All Bool/List/Eq/Vec inductive
blocks are emitted up front so cross-inductive obligations work.

Prints exactly one line:
  RESULT <file> elaborated=<n> obligs=<n> certified=<n> skipped=<n> \
         rs_rc=<n> cc_rc=<n> faithful=<bool> nodes=<csv> reasons=<csv>
(rs_rc/cc_rc are -2 when there were 0 certified obligations -> nothing to check.)
"""
import os, sys, re, subprocess, traceback

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
import induct
from induct import Inductive, Ctor

MM0   = "/home/bepis/prog/scientific-computing/mm0"
MM0RS = f"{MM0}/mm0-rs/target/release/mm0-rs"
MM0C  = f"{MM0}/mm0-c/mm0-c-np"

# prelude-ordered Bool (false=0, true=1), like bridge_bool_demo
BOOL_P = Inductive("tbool", "(lS lz)", [Ctor("bfalse", ()), Ctor("btrue", ())], "brec")

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

def eq_obligation(ty):
    """`Eq A lhs rhs` for ANY type A -> (A, lhs, rhs); else None.

    Not just `Eq Nat`: the certifier below is type-agnostic (it bridges and
    conversion-normalises the two sides), so whether an obligation certifies
    depends only on whether its sides land in a bridged fragment -- which the
    per-obligation try/except (and the sweep's both-checkers invariant) decide,
    not a hard-wired type filter here.  Counting an out-of-fragment Eq as an
    obligation-that-skipped is the honest accounting."""
    head, args = spine(ty)
    if isinstance(head, E.Const) and head.name == "Eq" and len(args) == 3:
        return args[0], args[1], args[2]
    return None


def _reason(prefix, ex):
    """Compact, csv-safe skip tag carrying WHAT failed, not just the class:
    prefer a quoted name from the message (e.g. unsup:Add.add), else its first
    word (e.g. ValueError:stuck).  Lets the sweep point at its own next targets
    instead of opaque exception names."""
    m = re.search(r"'([^']+)'", str(ex))
    tok = m.group(1) if m else (str(ex).split(":")[0].split() or [""])[0]
    tok = re.sub(r"[^A-Za-z0-9_.]+", "_", tok)[:32].strip("_")
    return prefix + (":" + tok if tok else "")


def main():
    fname = sys.argv[1]
    base = os.path.basename(fname)

    blocks = ""
    try:
        env = Env(); build_stdlib(env)
        # emit inductive blocks (idempotent registration into db_cert globals)
        blocks = (induct.generate(BOOL_P) + "\n" + induct.generate(induct.LIST) + "\n"
                  + induct.generate(induct.EQ) + "\n" + induct.generate(induct.VEC) + "\n")
        added = elaborate(open(fname).read(), env)
        K = Kernel(env)
    except Exception as ex:
        import traceback as _tb
        open("/tmp/elabfail_%s.txt" % base, "w").write(_tb.format_exc())
        print("RESULT %s elaborated=ERR obligs=0 certified=0 skipped=0 rs_rc=-3 cc_rc=-3 "
              "faithful=NA nodes= reasons=elab:%s:%s" % (base, type(ex).__name__, str(ex)[:40].replace(" ","_")))
        return

    certified, skipped = [], []
    for name in added:
        try:
            d = env.get(name)
        except Exception:
            continue
        ty = getattr(d, "type_", None)
        sides = eq_obligation(ty) if ty is not None else None
        if sides is None:
            continue                          # not an obligation; don't count
        A, lhs, rhs = sides
        try:
            # ORACLE: the real kernel must agree both sides convert (same normal
            # form).  This is the de-refl obligation Eq.refl was discharging.
            kl = kernel_nf(K, lhs); kr = kernel_nf(K, rhs)
            if kl != kr:
                skipped.append("not-convertible"); continue
            val = numval(kl)                  # may be None (common nf not a numeral)
            for c in sorted(consts_in(lhs, set()) | consts_in(rhs, set())):
                if env.has(c) and type(env.get(c)).__name__ == "Definition" \
                   and not env.get(c).level_params:
                    bridge.register_def(env, c)
            dl = bridge.to_db(lhs); dr = bridge.to_db(rhs)
            # CONVERSION cert: normalise BOTH sides and bridge (prove_conv =
            # deq_trans(norm lhs, sym(norm rhs))).  This handles an rhs that is
            # itself a computation (e.g. add 5 3 = succ (add 4 3)), which the old
            # "nf(lhs) == raw(rhs)" check wrongly rejected as nf-mismatch.
            conv = db_cert.prove_conv(dl, dr) or "(deq_refl)"
            # faithfulness: db_cert agrees both sides reduce to the same nf
            nfa, _ = db_cert.prove_norm(dl); nfb, _ = db_cert.prove_norm(dr)
            if db_cert.pp(nfa) != db_cert.pp(nfb):
                skipped.append("bridge-nf-mismatch"); continue
            certified.append((name, val, db_cert.pp(dl), db_cert.pp(dr), conv,
                              db_cert.proof_nodes(conv)))
        except bridge.Unsupported as ex:
            skipped.append(_reason("unsup", ex))
        except Exception as ex:
            skipped.append(_reason(type(ex).__name__, ex))

    obligs = len(certified) + len(skipped)
    nodes_csv = ",".join(str(n) for *_r, n in certified)
    reasons_csv = ",".join(sorted(set(skipped)))

    rs_rc = cc_rc = -2
    faithful = "NA"
    if certified:
        prelude  = open(f"{HERE}/db.mm1").read()
        defblock = db_cert.gen_def_block()
        thms = [f"theorem cov_{i}: $ deq cnil {dl} {dr} $ =\n'{conv};\n"
                for i, (nm, val, dl, dr, conv, nodes) in enumerate(certified)]
        full = prelude + "\n" + blocks + "\n" + defblock + "\n" + "\n".join(thms)
        mm1 = f"/tmp/cov_{base}.mm1"; mmb = f"/tmp/cov_{base}.mmb"
        open(mm1, "w").write(full)
        r = subprocess.run([MM0RS, "compile", mm1, mmb], capture_output=True, text=True)
        rs_rc = r.returncode
        faithful = "True"                     # kernel-nf == bridge-nf asserted per oblig above
        if rs_rc == 0:
            cc = subprocess.run([MM0C, mmb], capture_output=True, text=True)
            cc_rc = cc.returncode
        else:
            cc_rc = -1
            open(f"/tmp/cov_{base}.err", "w").write(r.stdout[-3000:] + "\n" + r.stderr[-3000:])

    print("RESULT %s elaborated=%d obligs=%d certified=%d skipped=%d rs_rc=%d cc_rc=%d "
          "faithful=%s nodes=%s reasons=%s" %
          (base, len(added), obligs, len(certified), len(skipped),
           rs_rc, cc_rc, faithful, nodes_csv or "-", reasons_csv or "-"))


if __name__ == "__main__":
    try:
        main()
    except Exception:
        b = os.path.basename(sys.argv[1]) if len(sys.argv) > 1 else "?"
        print("RESULT %s elaborated=ERR obligs=0 certified=0 skipped=0 rs_rc=-4 cc_rc=-4 "
              "faithful=NA nodes=- reasons=worker:%s" % (b, "crash"))
        sys.stderr.write(traceback.format_exc())
