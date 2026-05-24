"""CIC expression AST with de Bruijn indices.

Constructors:
  Sort  l            -- universe at level l
  BVar  i            -- bound variable (de Bruijn index)
  FVar  name type    -- free variable (locally constant, used during checking)
  Const name lvls    -- reference to a declaration in the env
  App   f a
  Lam   binder dom body
  Pi    binder dom body
  Let   binder type val body
"""
from __future__ import annotations
from dataclasses import dataclass, field
from typing import Union, Tuple, Optional
from .levels import Level, show as show_level


@dataclass(frozen=True)
class Sort:
    level: Level


@dataclass(frozen=True)
class BVar:
    idx: int


@dataclass(frozen=True)
class FVar:
    name: str          # unique within a checking context
    type_: "Expr"


@dataclass(frozen=True)
class Const:
    name: str
    levels: Tuple[Level, ...] = ()


@dataclass(frozen=True)
class App:
    fn: "Expr"
    arg: "Expr"


@dataclass(frozen=True)
class Lam:
    binder: str
    dom: "Expr"
    body: "Expr"


@dataclass(frozen=True)
class Pi:
    binder: str
    dom: "Expr"
    body: "Expr"
    implicit: bool = False         # `{x : T} → U`; elaborator inserts a meta
    inst_implicit: bool = False    # `[x : T] → U`; elaborator runs instance synth


@dataclass(frozen=True)
class Let:
    binder: str
    type_: "Expr"
    value: "Expr"
    body: "Expr"


@dataclass(frozen=True)
class Meta:
    """A metavariable introduced during elaboration.  After elaboration
    finishes, every Meta in the term must have been instantiated to a
    concrete term; the kernel never sees Metas."""
    id: int


@dataclass(frozen=True)
class Explicit:
    """`@f` marker — the elaborator must not auto-insert implicit or
    instance-implicit arguments for this head.  Stripped before the
    kernel sees the term."""
    inner: "Expr"


Expr = Union[Sort, BVar, FVar, Const, App, Lam, Pi, Let, Meta, Explicit]


# ---------------- shifting / substitution ----------------

def shift(e: Expr, d: int, cutoff: int = 0) -> Expr:
    """Add `d` to every BVar index ≥ cutoff."""
    if isinstance(e, BVar):
        return BVar(e.idx + d) if e.idx >= cutoff else e
    if isinstance(e, (Sort, FVar, Const, Meta)):
        return e
    if isinstance(e, Explicit):
        return Explicit(shift(e.inner, d, cutoff))
    if isinstance(e, App):
        return App(shift(e.fn, d, cutoff), shift(e.arg, d, cutoff))
    if isinstance(e, Lam):
        return Lam(e.binder, shift(e.dom, d, cutoff), shift(e.body, d, cutoff + 1))
    if isinstance(e, Pi):
        return Pi(e.binder, shift(e.dom, d, cutoff), shift(e.body, d, cutoff + 1),
                  e.implicit, e.inst_implicit)
    if isinstance(e, Let):
        return Let(e.binder, shift(e.type_, d, cutoff),
                   shift(e.value, d, cutoff),
                   shift(e.body, d, cutoff + 1))
    raise TypeError(e)


def subst_bvar(e: Expr, j: int, v: Expr) -> Expr:
    """Substitute `v` for BVar j in e.  Used in beta-reduction with j=0."""
    if isinstance(e, BVar):
        if e.idx == j:
            return shift(v, j)
        if e.idx > j:
            return BVar(e.idx - 1)        # bound variable was removed
        return e
    if isinstance(e, (Sort, FVar, Const, Meta)):
        return e
    if isinstance(e, Explicit):
        return Explicit(subst_bvar(e.inner, j, v))
    if isinstance(e, App):
        return App(subst_bvar(e.fn, j, v), subst_bvar(e.arg, j, v))
    if isinstance(e, Lam):
        return Lam(e.binder, subst_bvar(e.dom, j, v), subst_bvar(e.body, j + 1, v))
    if isinstance(e, Pi):
        return Pi(e.binder, subst_bvar(e.dom, j, v), subst_bvar(e.body, j + 1, v),
                  e.implicit, e.inst_implicit)
    if isinstance(e, Let):
        return Let(e.binder, subst_bvar(e.type_, j, v),
                   subst_bvar(e.value, j, v),
                   subst_bvar(e.body, j + 1, v))
    raise TypeError(e)


def beta(body: Expr, arg: Expr) -> Expr:
    """(λx. body) arg  ⟶  body[arg/x]"""
    return subst_bvar(body, 0, arg)


# -------- conversion between bound and free variables --------

def open_(e: Expr, fv: FVar) -> Expr:
    """Replace BVar 0 with fv (used when entering a binder)."""
    return subst_bvar(e, 0, fv)


def close(e: Expr, name: str, cutoff: int = 0) -> Expr:
    """Replace FVar(name,_) with BVar cutoff."""
    if isinstance(e, FVar):
        return BVar(cutoff) if e.name == name else e
    if isinstance(e, BVar):
        # Make room for the new binder by shifting outer BVars up.
        # (close is the inverse of open_, which decrements outer BVars.)
        return BVar(e.idx + 1) if e.idx >= cutoff else e
    if isinstance(e, (Sort, Const, Meta)):
        return e
    if isinstance(e, Explicit):
        return Explicit(close(e.inner, name, cutoff))
    if isinstance(e, App):
        return App(close(e.fn, name, cutoff), close(e.arg, name, cutoff))
    if isinstance(e, Lam):
        return Lam(e.binder, close(e.dom, name, cutoff), close(e.body, name, cutoff + 1))
    if isinstance(e, Pi):
        return Pi(e.binder, close(e.dom, name, cutoff), close(e.body, name, cutoff + 1),
                  e.implicit, e.inst_implicit)
    if isinstance(e, Let):
        return Let(e.binder, close(e.type_, name, cutoff),
                   close(e.value, name, cutoff),
                   close(e.body, name, cutoff + 1))
    raise TypeError(e)


# ----------------- level substitution -----------------

def inst_levels(e: Expr, params: Tuple[str, ...], args: Tuple[Level, ...]) -> Expr:
    """Substitute level args for level params throughout e."""
    from .levels import subst as lsubst
    env = dict(zip(params, args))
    if isinstance(e, Sort):
        return Sort(lsubst(e.level, env))
    if isinstance(e, Const):
        return Const(e.name, tuple(lsubst(l, env) for l in e.levels))
    if isinstance(e, (BVar, FVar, Meta)):
        return e
    if isinstance(e, Explicit):
        return Explicit(inst_levels(e.inner, params, args))
    if isinstance(e, App):
        return App(inst_levels(e.fn, params, args), inst_levels(e.arg, params, args))
    if isinstance(e, Lam):
        return Lam(e.binder, inst_levels(e.dom, params, args), inst_levels(e.body, params, args))
    if isinstance(e, Pi):
        return Pi(e.binder, inst_levels(e.dom, params, args), inst_levels(e.body, params, args),
                  e.implicit, e.inst_implicit)
    if isinstance(e, Let):
        return Let(e.binder, inst_levels(e.type_, params, args),
                   inst_levels(e.value, params, args),
                   inst_levels(e.body, params, args))
    raise TypeError


# ----------------- pretty -----------------

def show(e: Expr, depth: int = 0) -> str:
    if isinstance(e, Sort):
        return f"Sort {show_level(e.level)}"
    if isinstance(e, BVar):
        return f"#{e.idx}"
    if isinstance(e, FVar):
        return e.name
    if isinstance(e, Const):
        if e.levels:
            return f"{e.name}.{{{','.join(show_level(l) for l in e.levels)}}}"
        return e.name
    if isinstance(e, App):
        return f"({show(e.fn, depth)} {show(e.arg, depth)})"
    if isinstance(e, Lam):
        return f"(λ{e.binder}:{show(e.dom, depth)}. {show(e.body, depth+1)})"
    if isinstance(e, Pi):
        if e.binder.startswith("_"):
            return f"({show(e.dom, depth)} → {show(e.body, depth+1)})"
        if e.inst_implicit:
            open_b, close_b = ("[", "]")
        elif e.implicit:
            open_b, close_b = ("{", "}")
        else:
            open_b, close_b = ("", "")
        return f"(Π{open_b}{e.binder}:{show(e.dom, depth)}{close_b}. {show(e.body, depth+1)})"
    if isinstance(e, Meta):
        return f"?m{e.id}"
    if isinstance(e, Explicit):
        return f"@{show(e.inner, depth)}"
    if isinstance(e, Let):
        return f"(let {e.binder}:{show(e.type_, depth)} := {show(e.value, depth)} in {show(e.body, depth+1)})"
    raise TypeError(e)


# ----------------- builders -----------------

def app_many(f: Expr, *args: Expr) -> Expr:
    e = f
    for a in args:
        e = App(e, a)
    return e


def pi_many(*binders_and_body: object) -> Expr:
    """pi_many(("x", A), ("y", B), body)"""
    body = binders_and_body[-1]                   # type: ignore[assignment]
    assert isinstance(body, (Sort, BVar, FVar, Const, App, Lam, Pi, Let))
    for binder, dom in reversed(binders_and_body[:-1]):  # type: ignore[misc]
        body = Pi(binder, dom, body)
    return body


def lam_many(*binders_and_body: object) -> Expr:
    body = binders_and_body[-1]                   # type: ignore[assignment]
    assert isinstance(body, (Sort, BVar, FVar, Const, App, Lam, Pi, Let))
    for binder, dom in reversed(binders_and_body[:-1]):  # type: ignore[misc]
        body = Lam(binder, dom, body)
    return body
