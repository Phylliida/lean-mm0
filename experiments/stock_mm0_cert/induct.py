"""General (non-indexed, parameter-supporting) inductive types for the
de-Bruijn stock-MM0 prelude.

Given an inductive spec (type former, constructors with their fields, recursor),
`generate(ind)` emits the stock-MM0 axiom block -- term decls, shf/sub closure,
typing rules (ht_*), and per-constructor gated iota -- AND registers the
inductive into db_cert's registry so the certifier can typecheck/normalise
terms over it.  This is what `src/inductive.py` does internally, re-expressed
as pure stock-MM0 axioms with the reduction certified out of the trusted base.

Scope: non-indexed inductives in a single fixed universe, now WITH parameters
(uniform across constructors), so polymorphic List works in addition to Bool
and monomorphic ListNat.  Parameters thread through the type former, every
constructor, and the recursor; recursive occurrences reuse the same params.
Indexed inductives (Eq, Vec) are still harder and left as documented next steps.

Validation: regenerating Nat reproduces db.mm1's hand-written recursor type
verbatim (see run_induct.py) -- the correctness check for the de-Bruijn
index arithmetic.
"""
from __future__ import annotations
from dataclasses import dataclass, field as dfield
import db_cert
from db_cert import T, Var, App, Lam, Const, ESort, EPi, pp

# ---------------- named-binder term layer (for building schemas) ----------------
class N: pass
@dataclass(frozen=True)
class NVar(N):   name: str
@dataclass(frozen=True)
class NConst(N): name: str
@dataclass(frozen=True)
class NSort(N):  lvl: str
@dataclass(frozen=True)
class NApp(N):   f: N; a: N
@dataclass(frozen=True)
class NPi(N):    name: str; ty: N; body: N

def to_db(t: N, stack):
    """Convert a named term to de Bruijn, resolving NVar by nearest binder."""
    if isinstance(t, NVar):
        for k in range(len(stack) - 1, -1, -1):
            if stack[k] == t.name:
                return Var(len(stack) - 1 - k)
        raise KeyError(f"unbound {t.name!r}")
    if isinstance(t, NConst): return Const(t.name)
    if isinstance(t, NSort):  return ESort(t.lvl)
    if isinstance(t, NApp):   return App(to_db(t.f, stack), to_db(t.a, stack))
    if isinstance(t, NPi):    return EPi(to_db(t.ty, stack),
                                         to_db(t.body, stack + [t.name]))
    raise TypeError(t)

def napps(head: N, args):
    for a in args: head = NApp(head, a)
    return head

# ---------------- inductive spec ----------------
@dataclass(frozen=True)
class Fld:
    rec: bool                 # True = recursive occurrence of the type
    ty: object = None         # if non-rec: an N term for the (closed) field type

@dataclass(frozen=True)
class Ctor:
    name: str
    fields: tuple             # tuple[Fld]

@dataclass
class Inductive:
    tycon: str                # type-former const, e.g. "tbool"
    level: str                # MM0 level the *result* Sort inhabits
    ctors: list               # list[Ctor]
    rec_name: str             # recursor const, e.g. "brec"
    params: tuple = ()        # tuple[(name, N-kind)] uniform parameters, e.g.
                              #   (("A", NSort("(lS lz)")),) for List
    # filled in by _build():
    tycon_type: T = None      # full type former type (Pi params, Sort level)
    rec_type: T = None        # full recursor type
    ctor_types: dict = dfield(default_factory=dict)

# ---------------- schema construction ----------------
# All schemas are built with parameter binders in scope; `_tyapp` is the
# inductive applied to its parameters (the recursive-occurrence / result type).
def _tyapp(ind):
    return napps(NConst(ind.tycon), [NVar(n) for n, _ in ind.params])

def _wrap_params(ind, body):
    for name, kind in reversed(ind.params):
        body = NPi(name, kind, body)
    return body

def _ctor_type_N(ind, c):
    body = _tyapp(ind)
    for fl in reversed(c.fields):
        fty = _tyapp(ind) if fl.rec else fl.ty
        body = NPi("_", fty, body)
    return _wrap_params(ind, body)

def _minor_N(ind, c):
    """C (c params f0..fn)  wrapped by IHs (C f_r per rec field) then fields."""
    fnames = [f"f{i}" for i in range(len(c.fields))]
    capp = napps(NConst(c.name),
                 [NVar(n) for n, _ in ind.params] + [NVar(n) for n in fnames])
    body = NApp(NVar("C"), capp)
    for i in reversed(range(len(c.fields))):       # IHs, innermost-first
        if c.fields[i].rec:
            body = NPi("_", NApp(NVar("C"), NVar(fnames[i])), body)
    for i in reversed(range(len(c.fields))):       # field binders
        fty = _tyapp(ind) if c.fields[i].rec else c.fields[i].ty
        body = NPi(fnames[i], fty, body)
    return body

def _rec_type_N(ind):
    Tapp = _tyapp(ind)
    C_dom = NPi("_", Tapp, NSort(ind.level_u))     # C : (T params) -> Sort u
    body = NPi("x", Tapp, NApp(NVar("C"), NVar("x")))
    for c in reversed(ind.ctors):
        body = NPi("_", _minor_N(ind, c), body)
    return _wrap_params(ind, NPi("C", C_dom, body))

def _tycon_type_N(ind):
    return _wrap_params(ind, NSort(ind.level))

def _build(ind):
    ind.level_u = "u"                              # recursor is universe-poly in u
    ind.tycon_type = to_db(_tycon_type_N(ind), [])
    ind.rec_type = to_db(_rec_type_N(ind), [])
    for c in ind.ctors:
        ind.ctor_types[c.name] = to_db(_ctor_type_N(ind, c), [])

# ---------------- MM0 emission + registration ----------------
def _atoms(ind):
    return [ind.tycon] + [c.name for c in ind.ctors] + [ind.rec_name]

def generate(ind) -> str:
    _build(ind)
    # register into db_cert
    db_cert.TYCON[ind.tycon] = ind.tycon_type
    db_cert.REC_OF[ind.rec_name] = ind
    for i, c in enumerate(ind.ctors):
        db_cert.CTOR_IX[c.name] = (ind, i)
    for a in _atoms(ind):
        db_cert.ATOMIC.add(a)

    L = [f"-- ===== generated inductive: {ind.tycon} ====="]
    # term decls
    for a in _atoms(ind):
        L.append(f"term {a}: expr;")
    # shf / sub closure (atomic constants are unchanged by shift/subst)
    for a in _atoms(ind):
        L.append(f"axiom shf_{a} (d c: nat): $ shf {a} d c {a} $;")
    for a in _atoms(ind):
        L.append(f"axiom sub_{a} (v: expr) (j: nat): $ sub {a} v j {a} $;")
    # typing
    L.append(f"axiom ht_{ind.tycon} (g: ctx): $ ht g {ind.tycon} {pp(ind.tycon_type)} $;")
    for c in ind.ctors:
        L.append(f"axiom ht_{c.name} (g: ctx): $ ht g {c.name} {pp(ind.ctor_types[c.name])} $;")
    L.append(f"axiom ht_{ind.rec_name} (g: ctx) (u: lvl): "
             f"$ ht g {ind.rec_name} {pp(ind.rec_type)} $;")
    # gated iota, one per constructor
    L.append(_iota_axioms(ind))
    return "\n".join(L) + "\n"

def _iota_axioms(ind) -> str:
    k = len(ind.ctors)
    pvars = [f"p{i}" for i in range(len(ind.params))]
    mvars = [f"m{i}" for i in range(k)]
    rec_head = "(" + " @ ".join([ind.rec_name] + pvars + ["C"] + mvars) + ")"
    tyapp = "(" + " @ ".join([ind.tycon] + pvars) + ")" if pvars else ind.tycon
    out = []
    for j, c in enumerate(ind.ctors):
        fvars = [f"a{i}" for i in range(len(c.fields))]
        ctor_args = pvars + fvars
        capp = "(" + " @ ".join([c.name] + ctor_args) + ")" if ctor_args else c.name
        # contractum: m_j @ fields @ (rec_head @ f_r) for each rec field
        rhs = mvars[j]
        for fv in fvars:
            rhs = f"({rhs} @ {fv})"
        for i, fl in enumerate(c.fields):
            if fl.rec:
                rhs = f"({rhs} @ ({rec_head} @ {fvars[i]}))"
        binders = " ".join(pvars + ["C"] + mvars + fvars + ["mt"])
        out.append(
            f"axiom deq_iota_{c.name} (g: ctx) ({binders}: expr):\n"
            f"  $ ht g {rec_head} mt $ >\n"
            f"  $ ht g {capp} {tyapp} $ >\n"
            f"  $ deq g ({rec_head} @ {capp}) {rhs} $;")
    return "\n".join(out)


# ---------------- specs ----------------
NAT_T = NConst("tnat")

NAT = Inductive("tnat", "(lS lz)", [
    Ctor("tzero", ()),
    Ctor("tsucc", (Fld(rec=True),)),
], "trec")

BOOL = Inductive("tbool", "(lS lz)", [
    Ctor("btrue", ()),
    Ctor("bfalse", ()),
], "brec")

# ListNat: nil | cons (head : Nat) (tail : ListNat)
LNAT = Inductive("tlnat", "(lS lz)", [
    Ctor("lnil", ()),
    Ctor("lcons", (Fld(rec=False, ty=NAT_T), Fld(rec=True))),
], "lrec")

# Polymorphic List (A : Type) : nil | cons (head : A) (tail : List A)
#   parameter A lives at Sort 1 ("Type"); List A also at Sort 1.
LIST = Inductive("tlist", "(lS lz)", [
    Ctor("pnil", ()),
    Ctor("pcons", (Fld(rec=False, ty=NVar("A")), Fld(rec=True))),
], "prec", params=(("A", NSort("(lS lz)")),))
