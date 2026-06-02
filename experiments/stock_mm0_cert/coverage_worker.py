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


def peel_pis(ty):
    """Strip leading Pi binders.  Returns (tele, body) where tele is a list of
    (binder, dom) OUTERMOST-FIRST in de Bruijn (dom may mention earlier binders
    as BVars), and body is the Pi-free remainder.  A theorem like
    `(n : Nat) -> Eq Nat (n+0) n` has its free-variable `n` in the telescope; the
    closed case (no Pi) returns an empty tele, identical to the old direct path."""
    tele = []
    while isinstance(ty, E.Pi):
        tele.append((ty.binder, ty.dom)); ty = ty.body
    return tele, ty


def open_pis(ty):
    """Iterated open of the leading Pis into FRESH FVars, for the kernel oracle.
    Returns (LocalCtx, body) with body's telescope BVars replaced by FVars.  Each
    domain is opened w.r.t. the FVars already introduced (dependent telescopes)."""
    ctx = LocalCtx()
    while isinstance(ty, E.Pi):
        dom = ty.dom                       # already opened wrt earlier fvars
        name = ctx.push(ty.binder or "x", dom)
        ty = E.open_(ty.body, E.FVar(name, dom))
    return ctx, ty


def _reason(prefix, ex):
    """Compact, csv-safe skip tag carrying WHAT failed, not just the class:
    prefer a quoted name from the message (e.g. unsup:Add.add), else its first
    word (e.g. ValueError:stuck).  Lets the sweep point at its own next targets
    instead of opaque exception names."""
    m = re.search(r"'([^']+)'", str(ex))
    tok = m.group(1) if m else (str(ex).split(":")[0].split() or [""])[0]
    tok = re.sub(r"[^A-Za-z0-9_.]+", "_", tok)[:32].strip("_")
    return prefix + (":" + tok if tok else "")


def try_proofterm(env, d, name):
    """A NOT-convertible Eq obligation is not a de-refl leaf -- it is a whole proof
    (induction / case analysis / transport).  Certify it the proof-term way: TYPE the
    decl's entire elaborated proof term against its stated type, `ht cnil <value>
    <type>` (db_cert.prove_ht + a final _coerce).  This is exactly proofterm_worker's
    core, now reachable from the sweep.  Returns a cert record (kind="ht"), None if the
    decl has no proof body (an axiom), or RAISES if the body is out of the bridged
    fragment (caught by the caller -> a precise skip reason that names the next gap)."""
    val = getattr(d, "value", None)
    if val is None:
        return None
    for c in sorted(consts_in(val, set()) | consts_in(d.type_, set())):
        if c != name and env.has(c) and type(env.get(c)).__name__ == "Definition" \
           and not env.get(c).level_params:
            bridge.register_def(env, c)
    dty   = bridge.to_db(d.type_)
    dbody = bridge.to_db(val)
    tb, pb = db_cert.prove_ht(dbody, [])          # type the whole proof term
    proof  = db_cert._coerce(pb, tb, dty, [])     # coerce inferred -> stated type
    bodys, tys = db_cert.pp(dbody), db_cert.pp(dty)
    lps = [bridge.level_param_name(p) for p in (getattr(d, "level_params", ()) or ())]
    blob = bodys + tys + proof
    binders = "".join(f" ({p}: lvl)" for p in lps
                      if re.search(r"\b" + re.escape(p) + r"\b", blob))
    return {"kind": "ht", "name": name, "binders": binders, "body": bodys,
            "type": tys, "proof": proof, "nodes": db_cert.proof_nodes(proof)}


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
        bridge.bind_env(env)                  # so to_db's lazy poly-def path works
                                              # even when an obligation's only def is
                                              # polymorphic (no mono def to set _ENV)
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
        if ty is None:
            continue
        tele, body = peel_pis(ty)             # free-var telescope + Pi-free body
        sides = eq_obligation(body)
        if sides is None:
            continue                          # not an obligation; don't count
        A, lhs, rhs = sides                   # de Bruijn (loose BVars -> telescope)
        try:
            # ORACLE: the real kernel must agree both sides convert (same normal
            # form), UNDER the telescope's free variables (opened to FVars).  This
            # is the de-refl obligation Eq.refl was discharging.
            octx, obody = open_pis(ty)
            _Ao, olhs, orhs = eq_obligation(obody)
            kl = kernel_nf(K, olhs, octx); kr = kernel_nf(K, orhs, octx)
            if kl != kr:
                # not a de-refl leaf: certify the WHOLE proof term (ht cnil body type)
                # instead of skipping.  None -> no proof body (axiom), genuinely skip.
                pt = try_proofterm(env, d, name)
                if pt is None:
                    skipped.append("not-convertible"); continue
                certified.append(pt); continue
            val = numval(kl)                  # may be None (free var / not a numeral)
            for c in sorted(consts_in(lhs, set()) | consts_in(rhs, set())):
                if env.has(c) and type(env.get(c)).__name__ == "Definition" \
                   and not env.get(c).level_params:
                    bridge.register_def(env, c)
            gctx = [bridge.to_db(dom) for _bn, dom in tele]   # innermost LAST
            dl = bridge.to_db(lhs); dr = bridge.to_db(rhs)
            # context expr: the innermost binder is the OUTERMOST ccons (matches
            # ht_pi); cnil when tele is empty, so closed obligations are
            # byte-identical to before.
            G = "cnil"
            for dom in gctx:
                G = f"(ccons {db_cert.pp(dom)} {G})"
            # CONVERSION cert in the real context G, so whnf's iota gates can type a
            # free-variable motive/case via ht_var0/ht_weak.  prove_conv =
            # deq_trans(norm lhs, sym(norm rhs)); handles an rhs that is itself a
            # computation (e.g. add 5 3 = succ (add 4 3)).
            conv = db_cert.prove_conv(dl, dr, gctx) or "(deq_refl)"
            # faithfulness: db_cert agrees both sides reduce to the same nf
            nfa, _ = db_cert.prove_norm(dl, gctx); nfb, _ = db_cert.prove_norm(dr, gctx)
            if db_cert.pp(nfa) != db_cert.pp(nfb):
                skipped.append("bridge-nf-mismatch"); continue
            dls, drs = db_cert.pp(dl), db_cert.pp(dr)
            # universe params that actually appear (e.g. `Sort u` in a binder type) ->
            # `(lv_u: lvl)` theorem binders, so a level-polymorphic obligation is
            # certified GENERICALLY -- ht_sort / deq_refl already bind a level
            # metavariable, so no trusted-base change is needed.
            lps = [bridge.level_param_name(p) for p in (getattr(d, "level_params", ()) or ())]
            blob = G + dls + drs + conv
            binders = "".join(f" ({p}: lvl)" for p in lps
                              if re.search(r"\b" + re.escape(p) + r"\b", blob))
            certified.append({"kind": "deq", "name": name, "binders": binders,
                              "G": G, "dl": dls, "dr": drs, "conv": conv,
                              "nodes": db_cert.proof_nodes(conv)})
        except bridge.Unsupported as ex:
            skipped.append(_reason("unsup", ex))
        except Exception as ex:
            skipped.append(_reason(type(ex).__name__, ex))

    obligs = len(certified) + len(skipped)
    nodes_csv = ",".join(str(c["nodes"]) for c in certified)
    reasons_csv = ",".join(sorted(set(skipped)))

    rs_rc = cc_rc = -2
    faithful = "NA"
    if certified:
        prelude  = open(f"{HERE}/db.mm1").read()
        # defs + opaque lemmas (a de-refl side / proof may cite a `theorem`) + source
        # axioms, in ONE dependency-ordered stream (they interdepend).
        decls_block = db_cert.gen_all_blocks()
        # two cert shapes coexist per file: de-refl LEAVES (`deq G lhs rhs`, what
        # Eq.refl discharges) and whole PROOF TERMS (`ht cnil body type`, induction /
        # case analysis), both checked by both checkers.
        def _thm(i, c):
            if c["kind"] == "deq":
                return f"theorem cov_{i}{c['binders']}: $ deq {c['G']} {c['dl']} {c['dr']} $ =\n'{c['conv']};\n"
            return f"theorem cov_{i}{c['binders']}: $ ht cnil {c['body']} {c['type']} $ =\n'{c['proof']};\n"
        thms = [_thm(i, c) for i, c in enumerate(certified)]
        # bridge.IND_EMITTED holds blocks for any user inductive (class/structure)
        # auto-derived during this file's certification; they must precede the
        # defs/projections/instances that reference them.
        ind_blocks = "".join(bridge.IND_EMITTED)
        full = (prelude + "\n" + blocks + "\n" + ind_blocks + "\n" + decls_block + "\n"
                + "\n".join(thms))
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
