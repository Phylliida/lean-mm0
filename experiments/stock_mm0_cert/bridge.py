"""Kernel-integration spike: translate a REAL src/expr.py CIC term into the
db_cert de-Bruijn AST, so a genuine kernel term can be certified through
stock mm0-c -- instead of the hand-built demo terms used elsewhere here.

Scope (deliberately tiny -- this is one end-to-end data point, not the whole
pipeline): the closed Nat fragment.  Supported `Expr` nodes: Sort, BVar, App,
Lam, Pi, and Const for {Nat, Nat.zero, Nat.succ, Nat.rec}.  Everything else
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


# Map prelude Const names -> db.mm1 atomic constants (Nat fragment only).
# Map to db_cert's *singleton* Const objects, not fresh ones: db_cert.whnf's
# hard-wired Nat reduction path tests identity (`head is TREC`, `mj.f is TSUCC`,
# ...), so a fresh Const("trec") would never fire the recursor rule.
CONST_MAP = {
    "Nat":      db_cert.TNAT,
    "Nat.zero": db_cert.TZERO,
    "Nat.succ": db_cert.TSUCC,
    "Nat.rec":  db_cert.TREC,
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
    """src.expr.Expr  ->  db_cert.T   (Nat fragment, closed)."""
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
            return CONST_MAP[e.name]          # db_cert singleton (identity matters)
        raise Unsupported(f"Const {e.name!r} (not in the Nat fragment)")
    raise Unsupported(f"{type(e).__name__}")
