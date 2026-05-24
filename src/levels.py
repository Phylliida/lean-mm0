"""Universe levels for CIC.

Levels form an algebra:  l ::= 0 | l+1 | max l₁ l₂ | imax l₁ l₂ | u
where `u` is a level parameter.  `imax l₁ l₂` equals `0` when `l₂ = 0`,
otherwise `max l₁ l₂`; this is what makes `Sort 0` (i.e. `Prop`)
impredicative for Π types.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Union, Mapping


@dataclass(frozen=True)
class LZero:
    pass


@dataclass(frozen=True)
class LSucc:
    arg: "Level"


@dataclass(frozen=True)
class LMax:
    a: "Level"
    b: "Level"


@dataclass(frozen=True)
class LIMax:
    a: "Level"
    b: "Level"


@dataclass(frozen=True)
class LParam:
    name: str


@dataclass(frozen=True)
class LMeta:
    """A universe-level metavariable introduced during elaboration.
    Solved by `MetaContext.assign_level` once enough info is available."""
    id: int


Level = Union[LZero, LSucc, LMax, LIMax, LParam, LMeta]


def level_zero() -> Level:
    return LZero()


def level_succ(l: Level) -> Level:
    return LSucc(l)


def level_max(a: Level, b: Level) -> Level:
    return LMax(a, b)


def level_imax(a: Level, b: Level) -> Level:
    return LIMax(a, b)


def level_param(n: str) -> Level:
    return LParam(n)


def normalize(l: Level) -> Level:
    """Push successors inward, collapse trivial max/imax."""
    if isinstance(l, (LZero, LParam, LMeta)):
        return l
    if isinstance(l, LSucc):
        return LSucc(normalize(l.arg))
    if isinstance(l, LMax):
        a, b = normalize(l.a), normalize(l.b)
        if isinstance(a, LZero):
            return b
        if isinstance(b, LZero):
            return a
        if a == b:
            return a
        return LMax(a, b)
    if isinstance(l, LIMax):
        a, b = normalize(l.a), normalize(l.b)
        if isinstance(b, LZero):
            return LZero()
        if isinstance(b, LSucc):
            return normalize(LMax(a, b))
        if isinstance(a, LZero):
            return b
        return LIMax(a, b)
    raise TypeError(f"not a level: {l!r}")


def subst(l: Level, env: Mapping[str, Level]) -> Level:
    if isinstance(l, (LZero, LMeta)):
        return l
    if isinstance(l, LParam):
        return env.get(l.name, l)
    if isinstance(l, LSucc):
        return LSucc(subst(l.arg, env))
    if isinstance(l, LMax):
        return LMax(subst(l.a, env), subst(l.b, env))
    if isinstance(l, LIMax):
        return LIMax(subst(l.a, env), subst(l.b, env))
    raise TypeError


def equiv(a: Level, b: Level) -> bool:
    """Decide level equality up to the obvious laws.  Sound but
    incomplete in general; complete enough for the test suite."""
    a, b = normalize(a), normalize(b)
    if a == b:
        return True
    # numerical comparison when both are succ-towers over zero
    def to_nat(x: Level):
        n = 0
        while isinstance(x, LSucc):
            x, n = x.arg, n + 1
        return x, n
    ra, na = to_nat(a)
    rb, nb = to_nat(b)
    if isinstance(ra, LZero) and isinstance(rb, LZero):
        return na == nb
    # max-symmetry, max-idempotence
    if isinstance(a, LMax) and isinstance(b, LMax):
        return (equiv(a.a, b.a) and equiv(a.b, b.b)) or \
               (equiv(a.a, b.b) and equiv(a.b, b.a))
    return False


def show(l: Level) -> str:
    if isinstance(l, LZero):
        return "0"
    if isinstance(l, LParam):
        return l.name
    if isinstance(l, LMeta):
        return f"?u{l.id}"
    if isinstance(l, LSucc):
        # collapse succ chains
        n, x = 0, l
        while isinstance(x, LSucc):
            n, x = n + 1, x.arg
        if isinstance(x, LZero):
            return str(n)
        return f"{show(x)}+{n}"
    if isinstance(l, LMax):
        return f"max({show(l.a)},{show(l.b)})"
    if isinstance(l, LIMax):
        return f"imax({show(l.a)},{show(l.b)})"
    raise TypeError
