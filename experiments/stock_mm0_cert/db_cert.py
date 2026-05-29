"""Certifying evaluator for the DE-BRUIJN stock-MM0 prelude (db.mm1).

UNTRUSTED.  Generates explicit proofs of `shf` (shift), `sub` (subst), and
`deq` (definitional equality / reduction) against db.mm1's axioms.  Because
db.mm1 is de Bruijn, there are NO binder names -> no disjoint-variable
conditions, no alpha-renaming wall.  And because `deq` is untyped, the
conversion certificates carry no typing side-conditions.

This is the path the named lean.mm1 prelude could not reach: fully-concrete
ground recursor computations (e.g. 1+1=2), with shift/subst proven (out of
the trusted base) rather than computed.
"""
from __future__ import annotations
from dataclasses import dataclass

# ---------------- de Bruijn term AST (no names!) ----------------
class T: pass
@dataclass(frozen=True)
class Var(T): i: int
@dataclass(frozen=True)
class App(T): f: T; a: T
@dataclass(frozen=True)
class Lam(T): ty: T; body: T
@dataclass(frozen=True)
class Const(T): name: str

TNAT, TZERO, TSUCC, TREC = Const("tnat"), Const("tzero"), Const("tsucc"), Const("trec")

def natlit(n: int) -> str:
    return "nO" if n == 0 else f"(nS {natlit(n-1)})"

def pp(t: T) -> str:
    if isinstance(t, Var):   return f"(evar {natlit(t.i)})"
    if isinstance(t, App):   return f"({pp(t.f)} @ {pp(t.a)})"
    if isinstance(t, Lam):   return f"(elam {pp(t.ty)} {pp(t.body)})"
    if isinstance(t, Const): return t.name
    raise TypeError(t)

def uncurry(t: T):
    args = []
    while isinstance(t, App):
        args.append(t.a); t = t.f
    args.reverse(); return t, args

def curry(head: T, args):
    for a in args: head = App(head, a)
    return head

# ---------------- nat arithmetic certificates ----------------
def prove_padd(i: int, d: int):           # returns (k, proof of  padd i d k)
    if d == 0: return i, "(padd0)"
    k, p = prove_padd(i, d-1)
    return k+1, f"(paddS {p})"

def prove_nlt(a: int, b: int) -> str:     # proof of  nlt a b   (requires a < b)
    assert a < b, (a, b)
    if a == 0: return "(nlt0)"
    return f"(nltS {prove_nlt(a-1, b-1)})"

# ---------------- shift certificate:  shf e d c e' ----------------
def prove_shf(e: T, d: int, c: int):
    if isinstance(e, Const):
        return e, f"(shf_{ {'tnat':'nat','tzero':'zero','tsucc':'succ','trec':'rec'}[e.name] })"
    if isinstance(e, App):
        f2, pf = prove_shf(e.f, d, c); a2, pa = prove_shf(e.a, d, c)
        return App(f2, a2), f"(shf_app {pf} {pa})"
    if isinstance(e, Lam):
        t2, pt = prove_shf(e.ty, d, c); b2, pb = prove_shf(e.body, d, c+1)
        return Lam(t2, b2), f"(shf_lam {pt} {pb})"
    if isinstance(e, Var):
        if c == 0:
            k, pk = prove_padd(e.i, d)
            return Var(k), f"(shf_var_0 {pk})"
        if e.i == 0:
            return Var(0), "(shf_var_S0)"
        j_term, p = prove_shf(Var(e.i-1), d, c-1)   # j_term is Var(j)
        return Var(j_term.i + 1), f"(shf_var_SS {p})"
    raise TypeError(e)

# ---------------- subst certificate:  sub b v j b' ----------------
def prove_sub(b: T, v: T, j: int):
    if isinstance(b, Const):
        return b, f"(sub_{ {'tnat':'nat','tzero':'zero','tsucc':'succ','trec':'rec'}[b.name] })"
    if isinstance(b, App):
        f2, pf = prove_sub(b.f, v, j); a2, pa = prove_sub(b.a, v, j)
        return App(f2, a2), f"(sub_app {pf} {pa})"
    if isinstance(b, Lam):
        t2, pt = prove_sub(b.ty, v, j); bd2, pb = prove_sub(b.body, v, j+1)
        return Lam(t2, bd2), f"(sub_lam {pt} {pb})"
    if isinstance(b, Var):
        if b.i == j:
            v2, ps = prove_shf(v, j, 0)
            return v2, f"(sub_var_eq {ps})"
        if b.i < j:
            return Var(b.i), f"(sub_var_lt {prove_nlt(b.i, j)})"
        # b.i > j : decrement;  sub_var_gt needs  nlt j b.i
        return Var(b.i-1), f"(sub_var_gt {prove_nlt(j, b.i)})"
    raise TypeError(b)

# ---------------- deq / reduction certificate ----------------
def _trans(c1, c2):
    if c1 is None: return c2
    if c2 is None: return c1
    return f"(deq_trans {c1} {c2})"

def _app_cong(cf, ca):
    if cf is None and ca is None: return None
    return f"(deq_app {cf or '(deq_refl)'} {ca or '(deq_refl)'})"

def whnf(e: T):
    """Weak-head reduce; return (wh, conv|None) with conv proving deq cnil e wh."""
    if not isinstance(e, App):
        return e, None
    f_wh, cf = whnf(e.f)
    cong_f = _app_cong(cf, None) if cf else None
    if isinstance(f_wh, Lam):                       # beta redex
        b2, psub = prove_sub(f_wh.body, e.a, 0)
        wr, cr = whnf(b2)
        return wr, _trans(cong_f, _trans(f"(deq_beta {psub})", cr))
    g = App(f_wh, e.a)
    head, args = uncurry(g)
    if head is TREC and len(args) == 4:             # recursor redex
        C, z, s, major = args
        mj, cmj = whnf(major)
        cong_mj = f"(deq_app (deq_refl) {cmj})" if cmj else None
        if mj is TZERO:
            wz, cz = whnf(z)
            return wz, _trans(cong_f, _trans(cong_mj, _trans("(deq_iota_zero)", cz)))
        if isinstance(mj, App) and mj.f is TSUCC:
            k = mj.a
            contractum = App(App(s, k), curry(TREC, [C, z, s, k]))
            wc, cc = whnf(contractum)
            return wc, _trans(cong_f, _trans(cong_mj, _trans("(deq_iota_succ)", cc)))
    return g, cong_f

def prove_norm(e: T):
    """Full normal form; return (nf, conv|None) proving deq cnil e nf."""
    wh, c1 = whnf(e)
    if isinstance(wh, App):
        f2, cf = prove_norm(wh.f); a2, ca = prove_norm(wh.a)
        return App(f2, a2), _trans(c1, _app_cong(cf, ca))
    return wh, c1

def proof_nodes(proof: str) -> int:
    import re
    return len(re.findall(r'[A-Za-z_]\w*', proof))
