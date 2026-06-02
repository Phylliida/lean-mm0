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

# ---------------- registry of GENERATED inductives (populated by induct.py) ----
# Nat stays hard-wired (below) and benchmarked; these drive Bool/ListNat/etc.
TYCON   = {}   # tycon const name -> level string (the Sort it inhabits)
CTOR_IX = {}   # ctor const name  -> (ind, index)
REC_OF  = {}   # recursor name    -> ind
ATOMIC  = set()  # every generated atomic const name (for shf/sub closure)
DEFS    = {}   # def const name -> body T  (delta-unfold rides mm0's native
               # def-unfold; adds NO trusted axiom -- see gen_def_block)
OPAQUE  = {}   # opaque-lemma name -> (type T, body T, htop-proof str).  A `theorem`
               # (opaque proof) is checked ONCE -- emitted as an mm0 `def` plus a
               # `htop_<name> (g: ctx): ht g <body> <type>` theorem (g-polymorphic,
               # since a closed body's typing never pins the context) -- and every
               # USE of the lemma types by REFERENCE to that theorem, never re-typing
               # the body.  This is true opacity (modular proofs), with NO trusted
               # axiom: the lemma's typing is proved, not asserted.  See
               # gen_opaque_block / bridge.register_opaque.

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
        nat_names = {'tnat':'nat','tzero':'zero','tsucc':'succ','trec':'rec'}
        if e.name in nat_names:
            return e, f"(shf_{nat_names[e.name]})"
        if e.name in ATOMIC:
            return e, f"(shf_{e.name})"
        if e.name in DEFS:                   # closed def -> shift-invariant
            body = DEFS[e.name]
            b2, pb = prove_shf(body, d, c)
            assert b2 == body, f"def {e.name} body not shift-closed"
            return e, pb
        if e.name in OPAQUE:                  # opaque lemma = closed def -> invariant
            body = OPAQUE[e.name][1]
            b2, pb = prove_shf(body, d, c)
            assert b2 == body, f"opaque {e.name} body not shift-closed"
            return e, pb
        raise KeyError(f"shf: unknown const {e.name}")
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
        nat_names = {'tnat':'nat','tzero':'zero','tsucc':'succ','trec':'rec'}
        if b.name in nat_names:
            return b, f"(sub_{nat_names[b.name]})"
        if b.name in ATOMIC:
            return b, f"(sub_{b.name})"
        if b.name in DEFS:                   # closed def -> subst-invariant
            body = DEFS[b.name]
            b2, pb = prove_sub(body, v, j)
            assert b2 == body, f"def {b.name} body not subst-closed"
            return b, pb
        if b.name in OPAQUE:                  # opaque lemma = closed def -> invariant
            body = OPAQUE[b.name][1]
            b2, pb = prove_sub(body, v, j)
            assert b2 == body, f"opaque {b.name} body not subst-closed"
            return b, pb
        raise KeyError(f"sub: unknown const {b.name}")
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

def _is_nat(e: T, name: str) -> bool:
    """Is `e` the Nat-fragment const `name` (tnat/tzero/tsucc/trec)?  Compared by
    NAME, not identity: db_cert's reduction once relied on the four Nat singletons
    (to_db maps them to the module objects), but the `trec` TYPING rule returns
    `induct.NAT.rec_type`, which induct.py builds with fresh `Const("tzero")` /
    `Const("tsucc")` -- so a major substituted from that rec type is a non-singleton
    tzero.  Typing a real induction proof (e.g. zero_add's `add 0 0`) reduces such a
    major, so the gate must match by name.  Names tnat/tzero/tsucc/trec are reserved
    for Nat (generated inductives are sanitized + unique), so this is unambiguous."""
    return isinstance(e, Const) and e.name == name

def whnf(e: T, ctx=None):
    """Weak-head reduce; return (wh, conv|None) with conv proving deq G e wh.
    `ctx` (de-Bruijn binder types, innermost LAST) is threaded ONLY so the iota
    gates below can type a recursor's motive/cases in the real context when they
    mention free variables (ht_var0/ht_weak); the deq proof itself is context-
    polymorphic (every deq_* axiom leaves g a metavariable), so reduction is
    unchanged.  Defaults to the empty context, so closed callers are untouched."""
    if ctx is None: ctx = []
    if isinstance(e, Const) and e.name in DEFS:
        return whnf(DEFS[e.name], ctx)      # delta: unfold def -> body (free via
                                            # mm0 def-unfold; proof stays about body)
    if not isinstance(e, App):
        return e, None
    f_wh, cf = whnf(e.f, ctx)
    cong_f = _app_cong(cf, None) if cf else None
    if isinstance(f_wh, Lam):                       # beta redex
        b2, psub = prove_sub(f_wh.body, e.a, 0)
        wr, cr = whnf(b2, ctx)
        return wr, _trans(cong_f, _trans(f"(deq_beta {psub})", cr))
    g = App(f_wh, e.a)
    head, args = uncurry(g)
    if _is_nat(head, "trec") and len(args) == 4:    # recursor redex
        C, z, s, major = args
        # Fully NORMALISE the major (not just whnf): when the major is itself a
        # computation (e.g. Nat.add 8 9), whnf only exposes `succ K` with K an
        # unreduced recursor app, and the succ-iota gate prove_ht_nat(K) needs a
        # LITERAL numeral.  prove_norm reduces the major to succ^n zero, so the
        # predecessor k below is always a literal.  Fixes nested Nat.add.
        mj, cmj = prove_norm(major, ctx)
        cong_mj = f"(deq_app (deq_refl) {cmj})" if cmj else None
        if _is_nat(mj, "tzero"):
            gate = prove_rec_partial(C, z, s, ctx)   # ht (trec@C@z@s) (Pi m, C m)
            wz, cz = whnf(z, ctx)
            iota = f"(deq_iota_zero {gate})"
            return wz, _trans(cong_f, _trans(cong_mj, _trans(iota, cz)))
        if isinstance(mj, App) and _is_nat(mj.f, "tsucc"):
            k = mj.a
            gate = prove_rec_partial(C, z, s, ctx)
            hk = _ht_as_nat(k, ctx)                   # ht g k tnat (k numeral OR free var)
            iota = f"(deq_iota_succ {gate} {hk})"
            contractum = App(App(s, k), curry(TREC, [C, z, s, k]))
            wc, cc = whnf(contractum, ctx)
            return wc, _trans(cong_f, _trans(cong_mj, _trans(iota, cc)))
    # general (generated) inductive recursor.  Application layout:
    #   rec @ params(P) @ C @ minors(k) @ indices(I) @ major
    if isinstance(head, Const) and head.name in REC_OF:
        ind = REC_OF[head.name]
        P = len(ind.params)
        k = len(ind.ctors)
        I = len(ind.indices)
        if len(args) == P + 1 + k + I + 1:
            params = args[:P]
            C = args[P]
            minors = args[P + 1:P + 1 + k]
            major = args[P + 1 + k + I]
            mj, cmj = whnf(major, ctx)
            cong_mj = f"(deq_app (deq_refl) {cmj})" if cmj else None
            mh, fargs = uncurry(mj)        # fargs = params(P) ++ fields
            if isinstance(mh, Const) and mh.name in CTOR_IX \
               and CTOR_IX[mh.name][0] is ind:
                cidx = CTOR_IX[mh.name][1]
                c = ind.ctors[cidx]
                if len(fargs) == P + len(c.fields):
                    cfields = fargs[P:]
                    rec_prefix = list(params) + [C] + list(minors)
                    gate1 = prove_rec_partial_gen(ind, params, C, minors, ctx)
                    _t, gate2 = prove_ht(curry(Const(mh.name), fargs), ctx)
                    iota = f"(deq_iota_{mh.name} {gate1} {gate2})"
                    contr = curry(minors[cidx], cfields)
                    # recursive calls use each rec field's OWN index values (e.g.
                    # vcons's tail sits at index n, while the ctor outputs succ n)
                    rc_map = dict(ind.rec_calls(cidx, params, cfields))
                    for i, fl in enumerate(c.fields):
                        if fl.rec:
                            idxs = rc_map[i]
                            contr = App(contr,
                                        curry(head, rec_prefix + idxs + [cfields[i]]))
                    wc, cc = whnf(contr, ctx)
                    return wc, _trans(cong_f, _trans(cong_mj, _trans(iota, cc)))
    return g, cong_f

def prove_norm(e: T, ctx=None):
    """Full normal form; return (nf, conv|None) proving deq G e nf.
    Reduces under binders too (via deq_lam / deq_pi congruence); `ctx` is extended
    under each binder so a body's reductions type their gates in the right context.
    Defaults to the empty context, so closed callers are untouched."""
    if ctx is None: ctx = []
    wh, c1 = whnf(e, ctx)
    if isinstance(wh, App):
        f2, cf = prove_norm(wh.f, ctx); a2, ca = prove_norm(wh.a, ctx)
        return App(f2, a2), _trans(c1, _app_cong(cf, ca))
    if isinstance(wh, Lam):
        t2, ct = prove_norm(wh.ty, ctx); b2, cb = prove_norm(wh.body, ctx + [wh.ty])
        return Lam(t2, b2), _trans(c1, _deq_lam(ct, cb))
    if isinstance(wh, EPi):
        d2, cd = prove_norm(wh.dom, ctx); b2, cb = prove_norm(wh.body, ctx + [wh.dom])
        return EPi(d2, b2), _trans(c1, _deq_pi(cd, cb))
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

def prove_conv(A: T, B: T, ctx=None):
    """Proof of  deq G A B  (None = refl), assuming A and B are convertible.
    `ctx` is threaded so whnf's iota gates type free-variable motives/cases in the
    real context; defaults to empty, so closed callers are untouched."""
    if ctx is None: ctx = []
    nfa, ca = whnf(A, ctx); nfb, cb = whnf(B, ctx)
    return _trans(ca, _trans(_conv_structural(nfa, nfb, ctx), _sym(cb)))

def _conv_structural(A: T, B: T, ctx):
    if A == B: return None
    if isinstance(A, EPi) and isinstance(B, EPi):
        return _deq_pi(prove_conv(A.dom, B.dom, ctx),
                       prove_conv(A.body, B.body, ctx + [A.dom]))
    if isinstance(A, Lam) and isinstance(B, Lam):
        return _deq_lam(prove_conv(A.ty, B.ty, ctx),
                        prove_conv(A.body, B.body, ctx + [A.ty]))
    if isinstance(A, App) and isinstance(B, App):
        return _app_cong(prove_conv(A.f, B.f, ctx), prove_conv(A.a, B.a, ctx))
    if isinstance(A, ESort) and isinstance(B, ESort):
        return f"(deq_sort {prove_leveq(A.lvl, B.lvl)})"
    raise ValueError(f"cannot convert:\n  {pp(A)}\n  {pp(B)}")

# ---------------- typing certifier:  ht <ctx> e T ----------------
def prove_ht(e: T, ctx):
    """ctx is a list of de-Bruijn binder types, innermost LAST.
    Returns (type, proof) with proof : ht <ccons-of-ctx> e <type>."""
    if isinstance(e, ESort):
        return ESort(f"(lS {e.lvl})"), "(ht_sort)"
    if isinstance(e, Const):
        # compare by NAME, not identity: a `tnat` inside a generated schema is a
        # fresh Const("tnat"), not the module singleton TNAT.
        if e.name in OPAQUE:                          # opaque lemma: type by REFERENCE
            # cite the once-proved `htop_<name>`, do NOT re-type the body -- re-typing
            # at every use is the super-linear blow-up `theorem`/opacity exists to
            # avoid.  Sound with no trusted axiom; see bridge.register_opaque for why
            # this beats inlining (blow-up) and an asserted ht-axiom (unsound).
            return OPAQUE[e.name][0], f"(htop_{e.name})"
        if e.name in DEFS:    return prove_ht(DEFS[e.name], ctx)   # delta: type via body
        if e.name == "tnat":  return ESort("(lS lz)"), "(ht_nat)"
        if e.name == "tzero": return TNAT, "(ht_zero)"
        if e.name == "tsucc": return EPi(TNAT, TNAT), "(ht_succ)"
        if e.name in TYCON:   return TYCON[e.name], f"(ht_{e.name})"
        if e.name in CTOR_IX:
            ind, ix = CTOR_IX[e.name]
            return ind.ctor_types[e.name], f"(ht_{e.name})"
        if e.name in REC_OF:
            ind = REC_OF[e.name]
            return ind.rec_type, f"(ht_{ind.rec_name})"
        if e.name == "trec":
            # Nat's recursor, typed generically.  db.mm1's ht_rec axiom is
            # `ht_rec (g)(u: lvl)`: universe-poly in the motive level u, and
            # induct.NAT.rec_type reproduces that type verbatim (motive kind
            # `epi tnat (esort u)`).  The generic `u` is fine here -- when this
            # type is *applied* to a concrete motive, _coerce's level-unification
            # instantiates u to the motive's actual level (MM0 unifies the bound
            # var on its side), so u never reaches the closed level normalizer.
            import induct
            if induct.NAT.rec_type is None: induct._build(induct.NAT)
            return induct.NAT.rec_type, "(ht_rec)"
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
        if not isinstance(tf, EPi):
            # a function's type can be a stuck redex -- e.g. a recursor's result
            # type `C @ major` (C a lambda).  whnf it to expose the Pi, coercing
            # the proof across that (beta/delta/iota) conversion via ht_conv.
            nf, _c = whnf(tf, ctx)
            if isinstance(nf, EPi):
                pf = _coerce(pf, tf, nf, ctx); tf = nf
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
    if _levels_unify(have, want):
        # `want` becomes `have` by instantiating its free param levels (e.g. a
        # recursor's motive kind `epi tnat (esort u)` matched against the
        # concrete motive's `epi tnat (esort (lS lz))`).  MM0's ht_app unifies
        # that bound level var on its side, so NO ht_conv is needed -- emit the
        # proof bare, exactly as prove_rec_partial / prove_rec_partial_gen do.
        # Fail-safe: if the param isn't actually a bound metavar at the use site,
        # MM0 rejects the cert (both-checkers invariant) -- never a false accept.
        return proof
    nf_have, cnf = prove_norm(have, ctx)              # have may hide a param match
    if nf_have != have and _levels_unify(nf_have, want):  # behind an unreduced redex
        want_sort = _prove_sort(nf_have, ctx)
        return f"(ht_conv {proof} {cnf or '(deq_refl)'} {want_sort})"
    conv = prove_conv(have, want, ctx)
    want_sort = _prove_sort(want, ctx)                # ht ctx want (esort k)
    return f"(ht_conv {proof} {conv or '(deq_refl)'} {want_sort})"

def _prove_sort(B: T, ctx) -> str:
    """Proof of `ht ctx B (esort k)` for some concrete k -- B is a type.  This is
    ht_conv's well-formedness premise.  prove_ht(B) may give B's sort as an
    unreduced recursor-result redex (e.g. a sort-valued `brec`'s result type
    `brec_motive @ major` rather than a literal sort -- bool_dec_eq); normalise it
    to a literal `esort` and coerce, so MM0 sees a real sort (not `esort != eapp`)."""
    tB, pB = prove_ht(B, ctx)
    if isinstance(tB, ESort):
        return pB
    nf, c = prove_norm(tB, ctx)
    if isinstance(nf, ESort):
        _u, sortp = prove_ht(nf, ctx)                 # ht ctx (esort k) (esort (lS k))
        return f"(ht_conv {pB} {c or '(deq_refl)'} {sortp})"
    raise ValueError(f"type's sort did not normalise to esort: {pp(B)} : {pp(tB)}")

# ---- level unification: does `want` become `have` by instantiating want's params?
def _unify_lvl(ph, pw, subst):
    """Parsed levels ph (concrete-ish), pw (may contain params).  Bind each param
    in pw consistently to the matching subtree of ph.  Returns True on success."""
    if pw[0] == "param":
        name = pw[1]
        if name in subst: return subst[name] == ph
        subst[name] = ph; return True
    if ph[0] != pw[0]: return False
    if ph[0] == "lz": return True
    if ph[0] == "lS": return _unify_lvl(ph[1], pw[1], subst)
    if ph[0] in ("lmax", "limax"):
        return _unify_lvl(ph[1], pw[1], subst) and _unify_lvl(ph[2], pw[2], subst)
    return False

def _levels_unify(have, want, subst=None):
    """True iff `want` equals `have` after instantiating param levels appearing
    in `want` (term structure must match exactly; only ESort levels may differ)."""
    if subst is None: subst = {}
    if type(have) is not type(want): return False
    if isinstance(have, ESort):
        return _unify_lvl(_parse_level(have.lvl), _parse_level(want.lvl), subst)
    if isinstance(have, Var):   return have.i == want.i
    if isinstance(have, Const): return have.name == want.name
    if isinstance(have, App):
        return _levels_unify(have.f, want.f, subst) and _levels_unify(have.a, want.a, subst)
    if isinstance(have, Lam):
        return _levels_unify(have.ty, want.ty, subst) and _levels_unify(have.body, want.body, subst)
    if isinstance(have, EPi):
        return _levels_unify(have.dom, want.dom, subst) and _levels_unify(have.body, want.body, subst)
    return False

# ---- level instantiation: monomorphise a recursor type at a concrete motive level
def _subst_level_str(s, name, repl):
    import re
    return re.sub(rf"\b{re.escape(name)}\b", repl, s)

def inst_level(t: T, name: str, repl: str) -> T:
    """Substitute level string `repl` for the level param `name` in every ESort."""
    if isinstance(t, ESort): return ESort(_subst_level_str(t.lvl, name, repl))
    if isinstance(t, App):   return App(inst_level(t.f, name, repl), inst_level(t.a, name, repl))
    if isinstance(t, Lam):   return Lam(inst_level(t.ty, name, repl), inst_level(t.body, name, repl))
    if isinstance(t, EPi):   return EPi(inst_level(t.dom, name, repl), inst_level(t.body, name, repl))
    return t

def _codomain_sort(t: T) -> str:
    """Peel Pi binders off a motive kind `Pi .., esort k` and return the level k."""
    while isinstance(t, EPi): t = t.body
    if not isinstance(t, ESort):
        raise ValueError(f"motive codomain is not a sort: {pp(t)}")
    return t.lvl

# ---------------- recursor gating:  ht (trec @ cC @ z @ s) (Pi m, cC m) ----------------
# The recursor type tail R0 (motive C = evar 0), matching db.mm1's ht_rec.
_SUCC_CASE = EPi(TNAT, EPi(App(Var(2), Var(0)), App(Var(3), App(TSUCC, Var(1)))))
_R0 = EPi(App(Var(0), TZERO), EPi(_SUCC_CASE, EPi(TNAT, App(Var(3), Var(0)))))

def prove_rec_partial(cC: T, z: T, s: T, ctx=None) -> str:
    if ctx is None: ctx = []
    tcC, pcC = prove_ht(cC, ctx)                       # cC : epi tnat (esort u)
    R0sub, sub1 = prove_sub(_R0, cC, 0)                # R0[cC/0]
    p1 = f"(ht_app (ht_rec) {pcC} {sub1})"
    tz, pz = prove_ht(z, ctx)
    pz = _coerce(pz, tz, R0sub.dom, ctx)              # z : cC 0
    rest1 = R0sub.body
    rest1sub, sub2 = prove_sub(rest1, z, 0)
    p2 = f"(ht_app {p1} {pz} {sub2})"
    ts, ps = prove_ht(s, ctx)
    ps = _coerce(ps, ts, rest1sub.dom, ctx)           # s : Pi n, cC n -> cC (succ n)
    _r3, sub3 = prove_sub(rest1sub.body, s, 0)
    return f"(ht_app {p2} {ps} {sub3})"

def prove_rec_partial_gen(ind, params, C: T, minors, ctx=None) -> str:
    """ht g (<rec> @ params @ C @ minors...) (Pi x:(T params), C x).
    MONOMORPHISE the recursor type at u := k (read off C's normalised codomain),
    so no param level reaches the normaliser; MM0 unifies the axiom's bound u.
    `ctx` types the motive/minors when they mention free variables."""
    if ctx is None: ctx = []
    tC, pC = prove_ht(C, ctx)
    nf_tC, cC = prove_norm(tC, ctx)
    k = _codomain_sort(nf_tC)
    rec_type = inst_level(ind.rec_type, "u", k)
    if nf_tC != tC:
        _s, sortp = prove_ht(nf_tC, ctx)
        pC = f"(ht_conv {pC} {cC or '(deq_refl)'} {sortp})"; tC = nf_tC
    p = f"(ht_{ind.rec_name})"
    cur = rec_type
    plan = [(prm, None) for prm in params] + [(C, (pC, tC))] \
         + [(m, None) for m in minors]
    for arg, pre in plan:
        if pre is None:
            targ, parg = prove_ht(arg, ctx)
        else:
            parg, targ = pre
        parg = _coerce(parg, targ, cur.dom, ctx)
        res, subp = prove_sub(cur.body, arg, 0)
        p = f"(ht_app {p} {parg} {subp})"
        cur = res
    return p

def prove_ht_nat(e: T) -> str:
    """Proof of  ht G e tnat  for a numeral e (succ^n zero)."""
    if _is_nat(e, "tzero"):
        return "(ht_zero)"
    if isinstance(e, App) and _is_nat(e.f, "tsucc"):
        return f"(ht_app (ht_succ) {prove_ht_nat(e.a)} (sub_nat))"
    raise ValueError(f"not a numeral: {pp(e)}")

def _ht_as_nat(k: T, ctx) -> str:
    """Proof of  ht g k tnat.  Closed numerals take the lean context-free fast
    path (prove_ht_nat, preserving existing proof shapes); a succ-iota predecessor
    that is a FREE VARIABLE (e.g. `add m (succ n)` with n abstract) is typed in the
    real context instead (ht_var0/ht_weak), coerced to tnat."""
    try:
        return prove_ht_nat(k)
    except ValueError:
        tk, pk = prove_ht(k, ctx)
        return _coerce(pk, tk, TNAT, ctx)

def proof_nodes(proof: str) -> int:
    import re
    return len(re.findall(r'[A-Za-z_]\w*', proof))


def gen_def_block() -> str:
    """Emit a stock-MM0 `def` for every registered def, so delta-unfolding is
    mm0's OWN native def-unfold -- no trusted axiom per definition.  Emitted in
    insertion order; the caller registers dependencies (inductives, earlier
    defs) before the defs that use them."""
    return "".join(f"def {name}: expr = $ {pp(body)} $;\n" for name, body in DEFS.items())


def gen_opaque_block() -> str:
    """Emit each opaque lemma as an mm0 `def` (so its name is a real expr that
    unfolds to its body) PLUS a `htop_<name>` typing theorem proved ONCE.  No
    trusted axiom: the typing is *proved* (g-polymorphic, so it is usable in any
    context).  A use of the lemma references `(htop_<name>)` -- the body is never
    re-typed -- which is what makes modular proof chains scale (the kernel's whole
    reason for `theorem`/opaque-def).  Insertion order is dependency order (a
    lemma is registered after the lemmas its body cites).

    See bridge.register_opaque for the full reasoning: why this beats INLINING
    (reintroduces the super-linear blow-up opacity exists to avoid) and why an
    asserted `ht g L T` axiom would be UNSOUND (untyped deq breaks subject
    conversion).  The trick that needs no trusted axiom: a closed body's typing
    proof is context-polymorphic, so one `htop` theorem serves every use site."""
    out = []
    for name, (ty, body, proof) in OPAQUE.items():
        out.append(f"def {name}: expr = $ {pp(body)} $;")
        out.append(f"theorem htop_{name} (g: ctx): $ ht g {pp(body)} {pp(ty)} $ =\n"
                   f"'{proof};")
    return "\n".join(out) + ("\n" if out else "")


# ---------------- universe level normalisation: leveq certificates ----------------
def _parse_level(s):
    toks = s.replace("(", " ( ").replace(")", " ) ").split()
    pos = [0]
    def _close():
        assert toks[pos[0]] == ")", toks; pos[0] += 1
    def parse():
        t = toks[pos[0]]; pos[0] += 1
        if t == "(":
            op = toks[pos[0]]; pos[0] += 1
            if op == "lS":
                a = parse(); _close(); return ("lS", a)
            if op in ("lmax", "limax"):
                a = parse(); b = parse(); _close(); return (op, a, b)
            raise ValueError(f"level op {op}")
        if t == "lz": return ("lz",)
        return ("param", t)
    return parse()

def _max_num(na, nb):
    """na, nb closed numeral level strings -> (max numeral, leveq (lmax na nb) max)."""
    if na == "lz": return nb, "(leveq_max0l)"
    if nb == "lz": return na, "(leveq_max0r)"
    a2 = na[4:-1]; b2 = nb[4:-1]               # strip "(lS " ... ")"
    nm, pm = _max_num(a2, b2)
    return f"(lS {nm})", f"(leveq_trans (leveq_maxS) (leveq_S {pm}))"

def prove_norm_level(L):
    """parsed level -> (canonical numeral string, proof of leveq L numeral).
    Closed levels only (lz / lS / lmax / limax of closed levels)."""
    tag = L[0]
    if tag == "lz":   return "lz", "(leveq_refl)"
    if tag == "lS":
        n, p = prove_norm_level(L[1]); return f"(lS {n})", f"(leveq_S {p})"
    if tag == "lmax":
        na, pa = prove_norm_level(L[1]); nb, pb = prove_norm_level(L[2])
        nm, pm = _max_num(na, nb)
        return nm, f"(leveq_trans (leveq_max {pa} {pb}) {pm})"
    if tag == "limax":
        na, pa = prove_norm_level(L[1]); nb, pb = prove_norm_level(L[2])
        cong = f"(leveq_imax {pa} {pb})"
        if nb == "lz":
            return "lz", f"(leveq_trans {cong} (leveq_imax0))"
        nm, pm = _max_num(na, nb)
        return nm, f"(leveq_trans {cong} (leveq_trans (leveq_imaxS) {pm}))"
    raise ValueError(f"open/param level unsupported by the closed normalizer: {L}")

def prove_leveq(s1, s2):
    """Proof of  leveq s1 s2  for convertible CLOSED level strings."""
    if s1 == s2: return "(leveq_refl)"
    n1, p1 = prove_norm_level(_parse_level(s1))
    n2, p2 = prove_norm_level(_parse_level(s2))
    assert n1 == n2, f"levels not equal: {s1} ~> {n1}  vs  {s2} ~> {n2}"
    return f"(leveq_trans {p1} (leveq_sym {p2}))"

