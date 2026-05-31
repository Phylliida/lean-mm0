"""Kernel-integration spike: translate a REAL src/expr.py CIC term into the
db_cert de-Bruijn AST, so a genuine kernel term can be certified through
stock mm0-c -- instead of the hand-built demo terms used elsewhere here.

Scope (deliberately tiny -- this is one end-to-end data point, not the whole
pipeline): the closed Nat fragment, Bool, parametric List, and the indexed type Eq.  Supported `Expr` nodes: Sort, BVar, App,
Lam, Pi, and Const for {Nat,Nat.zero,Nat.succ,Nat.rec}, {Bool,Bool.false,Bool.true,Bool.rec}, {List,List.nil,List.cons,List.rec}, and {Eq,Eq.refl,Eq.rec}.  Everything else
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
}


from src.levels import LZero, LSucc


def level_to_str(l) -> str:
    """Translate a CIC Level to a db.mm1 level string (lz / (lS ...))."""
    if isinstance(l, LZero):
        return "lz"
    if isinstance(l, LSucc):
        return f"(lS {level_to_str(l.arg)})"
    raise Unsupported(f"level {l!r} (only closed lz/lS towers supported)")


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
        raise Unsupported(f"Const {e.name!r} (outside the bridged Nat/Bool/List fragments)")
    raise Unsupported(f"{type(e).__name__}")
