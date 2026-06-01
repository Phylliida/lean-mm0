"""Kernel-integration spike: translate a REAL src/expr.py CIC term into the
db_cert de-Bruijn AST, so a genuine kernel term can be certified through
stock mm0-c -- instead of the hand-built demo terms used elsewhere here.

Scope (deliberately tiny -- this is one end-to-end data point, not the whole
pipeline): the closed Nat fragment, Bool, parametric List, the indexed type Eq, and the recursive-indexed Vec; plus δ-unfolding of prelude `def`s (Nat.add, Nat.pred) via register_def.  Supported `Expr` nodes: Sort, BVar, App,
Lam, Pi, and Const for {Nat,Nat.zero,Nat.succ,Nat.rec}, {Bool,Bool.false,Bool.true,Bool.rec}, {List,List.nil,List.cons,List.rec}, {Eq,Eq.refl,Eq.rec}, and {Vec,Vec.nil,Vec.cons,Vec.rec}.  Everything else
raises Unsupported, on purpose, so we never silently mistranslate.

`src/expr.py` is ALREADY de Bruijn (BVar(idx)), and Nat.rec's argument order
(motive ++ minors ++ major, no params for Nat) matches db.mm1's
trec @ C @ z @ s @ major exactly -- so the translation is structural.

Faithfulness: bridge_demo.py cross-checks the db_cert normal form against the
real kernel's whnf-normalisation of the same term before certifying, so a
mistranslation can't pass unnoticed.
"""
from __future__ import annotations
import os, sys

# import the real kernel AST.  ROOT is the lean-mm0 dir (where the `src`
# package lives); `src.expr` is already de Bruijn.
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)
from src import expr as E
import db_cert
import induct
from db_cert import Var, App as TApp, Lam as TLam, Const as TConst, ESort, EPi


class Unsupported(Exception):
    pass


# Map prelude Const names -> db.mm1 / generated-block constants.
#
# Nat is special: db_cert.whnf's hard-wired Nat reduction path tests identity
# (`head is TREC`, `mj.f is TSUCC`, ...), so the four Nat names MUST map to
# db_cert's *singleton* Const objects -- a fresh Const("trec") would never fire
# the recursor rule.
#
# List (and any inductive emitted by induct.generate) goes through the GENERAL
# iota path, which matches by *name* against db_cert's registry (REC_OF /
# CTOR_IX), so fresh Const(name) objects are fine -- they just have to use the
# exact names the induct.py LIST spec registers (tlist / pnil / pcons / prec).
# The prelude term carries the universe level on the const (List.cons.{u}) and
# the element type as the first App arg (List.cons Nat ...); to_db drops the
# level and keeps the App args, which is precisely db_cert's param-as-arg
# convention.  So no structural change is needed -- only the name mapping below.
CONST_MAP = {
    # Nat fragment -- identity-mapped singletons (hard-wired whnf path)
    "Nat":       db_cert.TNAT,
    "Nat.zero":  db_cert.TZERO,
    "Nat.succ":  db_cert.TSUCC,
    "Nat.rec":   db_cert.TREC,
    # List fragment -- name-matched against the induct.generate(LIST) block;
    # names MUST equal induct.LIST's (tycon "tlist", ctors "pnil"/"pcons",
    # recursor "prec") or the general iota path never fires.
    "List":      TConst("tlist"),
    "List.nil":  TConst("pnil"),
    "List.cons": TConst("pcons"),
    "List.rec":  TConst("prec"),
    # Bool fragment -- name-matched.  The recursor selects its minor by ctor
    # POSITION, so the db_cert spec the demo registers must order the ctors the
    # way the prelude does (false=0, true=1).  induct.BOOL uses the opposite
    # order, so bridge_bool_demo.py registers its own prelude-ordered Bool spec
    # (ctors [bfalse, btrue]) rather than induct.BOOL.  Names are order-agnostic.
    "Bool":       TConst("tbool"),
    "Bool.false": TConst("bfalse"),
    "Bool.true":  TConst("btrue"),
    "Bool.rec":   TConst("brec"),
    # Eq fragment -- INDEXED inductive (J / large elimination); names match the
    # induct.EQ spec (tycon "teq", ctor "refl_eq", recursor "eqrec").  Eq's two
    # params (A, a) and one index (b) are all ordinary App args in the prelude
    # term (Eq.rec.{u,v} A a motive minor b major), matching db_cert's general
    # iota layout params ++ C ++ minors ++ indices ++ major -- still structural.
    "Eq":      TConst("teq"),
    "Eq.refl": TConst("refl_eq"),
    "Eq.rec":  TConst("eqrec"),
    # Vec fragment -- RECURSIVE + INDEXED; names match the induct.VEC spec
    # (tycon "tvec", ctors "vnil"/"vcons", recursor "vrec").  The prelude's
    # ctor order [Vec.nil, Vec.cons], Vec.cons field order [n, a, tail], and
    # Vec.rec arg order [A, C, minors, n, major] all match induct.VEC, so the
    # bridge stays structural and the shared spec is reused as-is.
    "Vec":      TConst("tvec"),
    "Vec.nil":  TConst("vnil"),
    "Vec.cons": TConst("vcons"),
    "Vec.rec":  TConst("vrec"),
}


from src.levels import LZero, LSucc


def level_to_str(l) -> str:
    """Translate a CIC Level to a db.mm1 level string (lz / (lS ...))."""
    if isinstance(l, LZero):
        return "lz"
    if isinstance(l, LSucc):
        return f"(lS {level_to_str(l.arg)})"
    raise Unsupported(f"level {l!r} (only closed lz/lS towers supported)")


def level_to_nat(l) -> int:
    """Closed level (lS-tower over lz) -> its numeral, for sanitized def names."""
    n = 0
    while isinstance(l, LSucc):
        n += 1; l = l.arg
    if isinstance(l, LZero):
        return n
    raise Unsupported(f"level {l!r} (only closed lz/lS towers supported)")


# Universe-polymorphic defs are MONOMORPHISED at each concrete use-site: a def
# `d.{u}` used as `d.{1}` becomes a distinct closed db_cert def `d_1` whose body
# is `inst_levels(d.value, d.level_params, [1])`.  MONO maps (name, level-strings)
# -> the db_cert Const for that instantiation; _ENV lets to_db lazily register a
# poly def the moment it meets it inside another body.  (db.mm1 erases the sort
# universe on inductives, so Nat/Bool/List stay level-agnostic in CONST_MAP; only
# *defs* whose bodies mention `Sort u` need per-instantiation monomorphisation.)
MONO = {}
_ENV = None

# --- user inductives (classes / structures) auto-bridged from the kernel ---
IND_EMITTED = []     # generated stock-MM0 blocks, in dependency (emission) order
IND_CONST = {}       # (kernel const name, level tag) -> db_cert TConst
_IND_REG = set()     # (inductive name, level tag) already generated


def to_db(e) -> object:
    """src.expr.Expr  ->  db_cert.T   (Nat / Bool / List fragments, closed)."""
    if isinstance(e, E.Sort):
        return ESort(level_to_str(e.level))
    if isinstance(e, E.BVar):
        return Var(e.idx)
    if isinstance(e, E.App):
        return TApp(to_db(e.fn), to_db(e.arg))
    if isinstance(e, E.Lam):
        return TLam(to_db(e.dom), to_db(e.body))
    if isinstance(e, E.Pi):
        return EPi(to_db(e.dom), to_db(e.body))
    if isinstance(e, E.Const):
        if e.name in CONST_MAP:
            return CONST_MAP[e.name]          # Nat -> singleton (identity); Bool/List -> named const (matched by name)
        # inductive tycon / ctor / recursor -- handle BEFORE the MONO-key below,
        # because a recursor's motive level can be an imax that level_to_str
        # (closed-tower only) won't render; the recursor mapping only needs the
        # type's first level anyway.
        tc = _try_inductive_const(e.name, e.levels)
        if tc is not None:
            return tc
        try:
            key = (e.name, tuple(level_to_str(l) for l in e.levels))
        except Unsupported:
            key = None                        # non-closed level: not a MONO key
        if key is not None and key in MONO:
            return MONO[key]                  # already-monomorphised poly def at these levels
        # lazy: a polymorphic def used at concrete levels -> monomorphise on demand
        if _ENV is not None and _ENV.has(e.name) \
           and type(_ENV.get(e.name)).__name__ == "Definition":
            return register_def(_ENV, e.name, e.levels)
        raise Unsupported(f"Const {e.name!r} (outside the bridged fragments)")
    raise Unsupported(f"{type(e).__name__}")


# ---------------- δ: register prelude definitions ----------------
def sanitize(name: str) -> str:
    """CIC const name -> a valid mm0 identifier (mm0 ids have no '.')."""
    return name.replace(".", "_").replace("'", "p")


def _consts_in(e, acc):
    if isinstance(e, E.Const):           acc.add(e.name)
    elif isinstance(e, E.App):           _consts_in(e.fn, acc); _consts_in(e.arg, acc)
    elif isinstance(e, (E.Lam, E.Pi)):   _consts_in(e.dom, acc); _consts_in(e.body, acc)
    return acc


def _register_mono_deps(env, name, body):
    """Eagerly register the MONOMORPHIC defs `body` uses (so they precede it in
    DEFS).  Polymorphic deps are left to to_db's lazy path, which registers them
    at their concrete use-site levels."""
    for c in sorted(_consts_in(body, set())):
        if c != name and env.has(c) and type(env.get(c)).__name__ == "Definition" \
           and not env.get(c).level_params:
            register_def(env, c)


def register_def(env, name, levels=()):
    """Register a Definition for delta and return its db_cert Const.

    Monomorphic defs key by name in CONST_MAP (as before).  Universe-polymorphic
    defs are MONOMORPHISED at the given concrete `levels`: the body is
    level-instantiated (inst_levels) into a closed term, keyed by (name, levels)
    in MONO under a sanitized name carrying the level tag (id_poly.{1} -> id_poly_1).
    Either way the bridged body lands in db_cert.DEFS, so delta rides mm0's native
    def-unfold and adds NO trusted axiom.  Idempotent."""
    global _ENV
    _ENV = env
    d = env.get(name)
    if type(d).__name__ != "Definition":
        raise Unsupported(f"{name!r} is not a Definition ({type(d).__name__})")

    if d.level_params:                       # polymorphic: monomorphise at `levels`
        if len(levels) != len(d.level_params):
            raise Unsupported(f"{name!r} needs {len(d.level_params)} levels, got {len(levels)}")
        key = (name, tuple(level_to_str(l) for l in levels))
        if key in MONO:
            return MONO[key]
        body = E.inst_levels(d.value, d.level_params, tuple(levels))
        san = sanitize(name) + "_" + "_".join(str(level_to_nat(l)) for l in levels)
        MONO[key] = TConst(san)              # placeholder first (breaks cycles)
        try:                                 # ...but roll it back on failure, so a
            _register_mono_deps(env, name, body)         # partial registration can't
            db_cert.DEFS[san] = to_db(body)  # poison later obligations with a body-
        except Exception:                    # less const (each oblig fails on its own
            MONO.pop(key, None); db_cert.DEFS.pop(san, None); raise   # true reason)
        return MONO[key]

    if name in CONST_MAP:                     # monomorphic
        return CONST_MAP[name]
    body = d.value
    san = sanitize(name)
    CONST_MAP[name] = TConst(san)            # placeholder first (so to_db maps name -> san)
    try:                                     # atomic: roll back on failure (see poly path)
        _register_mono_deps(env, name, body)
        db_cert.DEFS[san] = to_db(body)
    except Exception:
        CONST_MAP.pop(name, None); db_cert.DEFS.pop(san, None); raise
    return CONST_MAP[name]


# ---------------- auto-bridge user inductives (classes / structures) ----------
# A `class`/`structure` desugars to a parametric single-constructor Inductive; an
# `inductive` to a multi-ctor one.  Rather than hand-write a db.mm1 block per
# type (as for Nat/Bool/List/Eq/Vec), derive the induct.py spec straight from the
# kernel's Inductive/Constructor/Recursor decls, monomorphised at the use-site
# levels, and let induct.generate emit the stock-MM0 axioms + register them.  The
# projection and instance are ordinary Definitions and ride the delta path above.
def _peel(e, n):
    bs = []
    for _ in range(n):
        if not isinstance(e, E.Pi):
            raise Unsupported("expected Pi while peeling an inductive telescope")
        bs.append((e.binder, e.dom)); e = e.body
    return bs, e


def _spine(e):
    args = []
    while isinstance(e, E.App):
        args.append(e.arg); e = e.fn
    args.reverse()
    return e, args


def _whnf_delta(e):
    """δ-unfold definitions at the head (+ β) on a raw kernel Expr, so a field /
    index type whose head is a `def` (e.g. `Not p` := `p -> False`) is exposed as
    its unfolding before translation.  Loose BVars are fine -- this does no
    typing, only head reduction.  Inlining keeps field types as concrete
    structural terms (the def never enters the emitted block, so there is no
    def-before-inductive ordering constraint)."""
    for _ in range(10000):                       # guard a pathological def cycle
        head, args = _spine(e)
        if isinstance(head, E.Const) and _ENV is not None and _ENV.has(head.name) \
           and type(_ENV.get(head.name)).__name__ == "Definition":
            d = _ENV.get(head.name)
            val = (E.inst_levels(d.value, tuple(d.level_params), tuple(head.levels))
                   if d.level_params else d.value)
            for a in args:                       # β-apply the spine args
                val = E.beta(val.body, a) if isinstance(val, E.Lam) else E.App(val, a)
            e = val
            continue
        return e
    raise Unsupported("delta-unfolding did not terminate in a field/index type")


def _expr_to_N(e, stack, iname):
    """kernel Expr (closed over `stack`, a list of binder names innermost-last)
    -> an induct.N named term, for use in an induct.py inductive spec.  Defs in
    the type are inlined (δ); references to *other* user inductives are registered
    (so their block is emitted first) and used by their generated name."""
    e = _whnf_delta(e)                            # inline any def at the head
    if isinstance(e, E.Sort):
        return induct.NSort(level_to_str(e.level))
    if isinstance(e, E.BVar):
        if e.idx >= len(stack):
            raise Unsupported(f"free BVar {e.idx} in an inductive type")
        return induct.NVar(stack[len(stack) - 1 - e.idx])
    if isinstance(e, E.Pi):
        bn = e.binder or "_"
        return induct.NPi(bn, _expr_to_N(e.dom, stack, iname),
                          _expr_to_N(e.body, stack + [bn], iname))
    if isinstance(e, E.App):
        return induct.NApp(_expr_to_N(e.fn, stack, iname),
                           _expr_to_N(e.arg, stack, iname))
    if isinstance(e, E.Const):
        if e.name in CONST_MAP:                   # already-bridged base const
            return induct.NConst(CONST_MAP[e.name].name)
        tc = _try_inductive_const(e.name, e.levels)   # another user inductive
        if tc is not None:                            # (registered + emitted first)
            return induct.NConst(tc.name)
        raise Unsupported(f"const {e.name!r} in an inductive field/index type")
    raise Unsupported(f"inductive type node {type(e).__name__}")


def register_inductive(env, iname, levels):
    """Derive + emit + register a kernel Inductive (monomorphised at `levels`).
    Idempotent.  Covers parametric inductives whose constructor fields are
    non-recursive (records: classes/structures like Add/Mul/Pair -- the dominant
    skip cluster) and, in general, the recursive/indexed shapes induct.py
    supports, provided field/index types stay within the bridged base."""
    global _ENV
    _ENV = env                                   # so _whnf_delta / _try_inductive_const resolve
    ind = env.get(iname)
    if type(ind).__name__ != "Inductive":
        raise Unsupported(f"{iname!r} is not an Inductive")
    tag = "_".join(str(level_to_nat(l)) for l in levels)
    if (iname, tag) in _IND_REG:
        return
    lp = ind.level_params
    inst = (lambda e: E.inst_levels(e, lp, tuple(levels))) if lp else (lambda e: e)
    P, X = ind.num_params, ind.num_indices
    san = lambda nm: sanitize(nm) + ("_" + tag if tag else "")

    tbinders, tbody = _peel(inst(ind.type_), P + X)
    pnames = [b[0] or f"p{i}" for i, b in enumerate(tbinders[:P])]
    xnames = [b[0] or f"x{i}" for i, b in enumerate(tbinders[P:])]
    stack, Nparams, Nindices = [], [], []
    for nm, (_bn, dom) in zip(pnames, tbinders[:P]):
        Nparams.append((nm, _expr_to_N(dom, stack, iname))); stack.append(nm)
    for nm, (_bn, dom) in zip(xnames, tbinders[P:]):
        Nindices.append((nm, _expr_to_N(dom, stack, iname))); stack.append(nm)
    if not isinstance(tbody, E.Sort):
        raise Unsupported(f"{iname}: inductive result is not a Sort")
    level = level_to_str(tbody.level)

    Nctors, cmap = [], {}
    for cn in ind.constructor_names:
        c = env.get(cn)
        cb, cbody = _peel(inst(c.type_), P + c.num_fields)
        fstack, flds = list(pnames), []
        for fi, (_bn, dom) in enumerate(cb[P:]):
            fname = _bn or f"f{fi}"
            h, hargs = _spine(dom)
            if isinstance(h, E.Const) and h.name == iname:           # recursive field
                rivs = [_expr_to_N(a, fstack, iname) for a in hargs[P:]]
                flds.append(induct.Fld(rec=True, name=fname,
                                       rec_index_vals=tuple(rivs)))
            else:
                flds.append(induct.Fld(rec=False, name=fname,
                                       ty=_expr_to_N(dom, fstack, iname)))
            fstack.append(fname)
        _h, cargs = _spine(cbody)
        ivs = [_expr_to_N(a, fstack, iname) for a in cargs[P:]]       # output indices
        gcn = san(cn); cmap[cn] = gcn
        Nctors.append(induct.Ctor(gcn, tuple(flds), index_vals=tuple(ivs)))

    spec = induct.Inductive(san(iname), level, Nctors, san(ind.recursor_name),
                            params=tuple(Nparams), indices=tuple(Nindices))
    IND_EMITTED.append(induct.generate(spec))
    _IND_REG.add((iname, tag))
    IND_CONST[(iname, tag)] = TConst(san(iname))
    IND_CONST[(ind.recursor_name, tag)] = TConst(san(ind.recursor_name))
    for kn, gcn in cmap.items():
        IND_CONST[(kn, tag)] = TConst(gcn)


def _try_inductive_const(name, levels):
    """If `name` is the tycon / a constructor / the recursor of a kernel
    Inductive, ensure that inductive is registered (at the *type's* levels) and
    return this const's db_cert TConst.  Else None."""
    if _ENV is None or not _ENV.has(name):
        return None
    d = _ENV.get(name); kind = type(d).__name__
    if kind == "Inductive":
        iname, tlevels = name, levels
    elif kind == "Constructor":
        iname, tlevels = d.inductive, levels
    elif kind == "Recursor":
        iname = d.inductive
        tlevels = levels[:len(_ENV.get(iname).level_params)]
    else:
        return None
    register_inductive(_ENV, iname, tlevels)
    tag = "_".join(str(level_to_nat(l)) for l in tlevels)
    return IND_CONST.get((name, tag))
