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
        key = (e.name, tuple(level_to_str(l) for l in e.levels))
        if key in MONO:
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
        _register_mono_deps(env, name, body)
        db_cert.DEFS[san] = to_db(body)      # to_db lazily registers nested poly defs
        return MONO[key]

    if name in CONST_MAP:                     # monomorphic
        return CONST_MAP[name]
    body = d.value
    san = sanitize(name)
    CONST_MAP[name] = TConst(san)            # placeholder first (so to_db maps name -> san)
    _register_mono_deps(env, name, body)
    db_cert.DEFS[san] = to_db(body)
    return CONST_MAP[name]
