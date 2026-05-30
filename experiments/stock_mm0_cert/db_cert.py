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
@dataclass(frozen=True)
class ESort(T): lvl: str            # esort l   (l a level string: "lz", "(lS lz)")
@dataclass(frozen=True)
class EPi(T): dom: T; body: T       # epi DOMAIN BODY

TNAT, TZERO, TSUCC, TREC = Const("tnat"), Const("tzero"), Const("tsucc"), Const("trec")

def natlit(n: int) -> str:
    return "nO" if n == 0 else f"(nS {natlit(n-1)})"

def pp(t: T) -> str:
    if isinstance(t, Var):   return f"(evar {natlit(t.i)})"
    if isinstance(t, App):   return f"({pp(t.f)} @ {pp(t.a)})"
    if isinstance(t, Lam):   return f"(elam {pp(t.ty)} {pp(t.body)})"
    if isinstance(t, EPi):   return f"(epi {pp(t.dom)} {pp(t.body)})"
    if isinstance(t, ESort): return f"(esort {t.lvl})"
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
    if isinstance(e, EPi):
        t2, pt = prove_shf(e.dom, d, c); b2, pb = prove_shf(e.body, d, c+1)
        return EPi(t2, b2), f"(shf_pi {pt} {pb})"
    if isinstance(e, ESort):
        return e, "(shf_sort)"
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
    if isinstance(b, EPi):
        t2, pt = prove_sub(b.dom, v, j); bd2, pb = prove_sub(b.body, v, j+1)
        return EPi(t2, bd2), f"(sub_pi {pt} {pb})"
    if isinstance(b, ESort):
        return b, "(sub_sort)"
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
            gate = prove_rec_partial(C, z, s)        # ht (trec@C@z@s) (Pi m, C m)
            wz, cz = whnf(z)
            iota = f"(deq_iota_zero {gate})"
            return wz, _trans(cong_f, _trans(cong_mj, _trans(iota, cz)))
        if isinstance(mj, App) and mj.f is TSUCC:
            k = mj.a
            gate = prove_rec_partial(C, z, s)
            hk = prove_ht_nat(k)                      # ht k tnat
            iota = f"(deq_iota_succ {gate} {hk})"
            contractum = App(App(s, k), curry(TREC, [C, z, s, k]))
            wc, cc = whnf(contractum)
            return wc, _trans(cong_f, _trans(cong_mj, _trans(iota, cc)))
    return g, cong_f

def prove_norm(e: T):
    """Full normal form; return (nf, conv|None) proving deq cnil e nf."""
    wh, c1 = whnf(e)
    if isinstance(wh, App):
        f2, cf = prove_norm(wh.f); a2, ca = prove_norm(wh.a)
        return App(f2, a2), _trans(c1, _app_cong(cf, ca))
    return wh, c1

# ---------------- conversion-proof generator:  deq g A B ----------------
def _sym(c):
    return None if c is None else f"(deq_sym {c})"
def _deq_pi(cd, cb):
    if cd is None and cb is None: return None
    return f"(deq_pi {cd or '(deq_refl)'} {cb or '(deq_refl)'})"
def _deq_lam(cd, cb):
    if cd is None and cb is None: return None
    return f"(deq_lam {cd or '(deq_refl)'} {cb or '(deq_refl)'})"

def prove_conv(A: T, B: T):
    """Proof of  deq g A B  (None = refl), assuming A and B are convertible."""
    nfa, ca = whnf(A); nfb, cb = whnf(B)
    return _trans(ca, _trans(_conv_structural(nfa, nfb), _sym(cb)))

def _conv_structural(A: T, B: T):
    if A == B: return None
    if isinstance(A, EPi) and isinstance(B, EPi):
        return _deq_pi(prove_conv(A.dom, B.dom), prove_conv(A.body, B.body))
    if isinstance(A, Lam) and isinstance(B, Lam):
        return _deq_lam(prove_conv(A.ty, B.ty), prove_conv(A.body, B.body))
    if isinstance(A, App) and isinstance(B, App):
        return _app_cong(prove_conv(A.f, B.f), prove_conv(A.a, B.a))
    raise ValueError(f"cannot convert:\n  {pp(A)}\n  {pp(B)}")

# ---------------- typing certifier:  ht <ctx> e T ----------------
def prove_ht(e: T, ctx):
    """ctx is a list of de-Bruijn binder types, innermost LAST.
    Returns (type, proof) with proof : ht <ccons-of-ctx> e <type>."""
    if isinstance(e, ESort):
        return ESort(f"(lS {e.lvl})"), "(ht_sort)"
    if isinstance(e, Const):
        if e is TNAT:  return ESort("(lS lz)"), "(ht_nat)"
        if e is TZERO: return TNAT, "(ht_zero)"
        if e is TSUCC: return EPi(TNAT, TNAT), "(ht_succ)"
        raise ValueError(f"no typing rule for {e.name}")
    if isinstance(e, Var):
        return _ht_var(e.i, ctx)
    if isinstance(e, EPi):
        ua, pa = prove_ht(e.dom, ctx)
        ub, pb = prove_ht(e.body, ctx + [e.dom])
        return ESort(f"(limax {ua.lvl} {ub.lvl})"), f"(ht_pi {pa} {pb})"
    if isinstance(e, Lam):
        _ua, pa = prove_ht(e.ty, ctx)                 # ty is a type (esort u)
        tb, pb = prove_ht(e.body, ctx + [e.ty])
        return EPi(e.ty, tb), f"(ht_lam {pa} {pb})"
    if isinstance(e, App):
        tf, pf = prove_ht(e.f, ctx)
        assert isinstance(tf, EPi), f"applying non-Pi {pp(tf)}"
        ta, pa = prove_ht(e.a, ctx)
        pa = _coerce(pa, ta, tf.dom, ctx)
        b2, psub = prove_sub(tf.body, e.a, 0)
        return b2, f"(ht_app {pf} {pa} {psub})"
    raise TypeError(e)

def _ht_var(i, ctx):
    base = ctx[len(ctx)-1-i]
    if i == 0:
        sh, psh = prove_shf(base, 1, 0)
        return sh, f"(ht_var0 {psh})"
    ity, ip = _ht_var(i-1, ctx[:-1])
    sh, psh = prove_shf(ity, 1, 0)
    return sh, f"(ht_weak {ip} {psh})"

def _coerce(proof, have, want, ctx):
    if have == want:
        return proof
    conv = prove_conv(have, want)
    _u, want_sort = prove_ht(want, ctx)               # ht ctx want (esort u)
    return f"(ht_conv {proof} {conv or '(deq_refl)'} {want_sort})"

# ---------------- recursor gating:  ht (trec @ cC @ z @ s) (Pi m, cC m) ----------------
# The recursor type tail R0 (motive C = evar 0), matching db.mm1's ht_rec.
_SUCC_CASE = EPi(TNAT, EPi(App(Var(2), Var(0)), App(Var(3), App(TSUCC, Var(1)))))
_R0 = EPi(App(Var(0), TZERO), EPi(_SUCC_CASE, EPi(TNAT, App(Var(3), Var(0)))))

def prove_rec_partial(cC: T, z: T, s: T) -> str:
    tcC, pcC = prove_ht(cC, [])                        # cC : epi tnat (esort u)
    R0sub, sub1 = prove_sub(_R0, cC, 0)                # R0[cC/0]
    p1 = f"(ht_app (ht_rec) {pcC} {sub1})"
    tz, pz = prove_ht(z, [])
    pz = _coerce(pz, tz, R0sub.dom, [])               # z : cC 0
    rest1 = R0sub.body
    rest1sub, sub2 = prove_sub(rest1, z, 0)
    p2 = f"(ht_app {p1} {pz} {sub2})"
    ts, ps = prove_ht(s, [])
    ps = _coerce(ps, ts, rest1sub.dom, [])            # s : Pi n, cC n -> cC (succ n)
    _r3, sub3 = prove_sub(rest1sub.body, s, 0)
    return f"(ht_app {p2} {ps} {sub3})"

def prove_ht_nat(e: T) -> str:
    """Proof of  ht G e tnat  for a numeral e (succ^n zero)."""
    if e is TZERO:
        return "(ht_zero)"
    if isinstance(e, App) and e.f is TSUCC:
        return f"(ht_app (ht_succ) {prove_ht_nat(e.a)} (sub_nat))"
    raise ValueError(f"not a numeral: {pp(e)}")

def proof_nodes(proof: str) -> int:
    import re
    return len(re.findall(r'[A-Za-z_]\w*', proof))
