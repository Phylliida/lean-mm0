"""General inductive types (parameters + indices) for the de-Bruijn
stock-MM0 prelude.

Given an inductive spec (type former, constructors with their fields, recursor),
`generate(ind)` emits the stock-MM0 axiom block -- term decls, shf/sub closure,
typing rules (ht_*), and per-constructor gated iota -- AND registers the
inductive into db_cert's registry so the certifier can typecheck/normalise
terms over it.  This is what `src/inductive.py` does internally, re-expressed
as pure stock-MM0 axioms with the reduction certified out of the trusted base.

Scope: single fixed universe, with PARAMETERS (uniform across constructors)
and INDICES (varying per constructor), including the RECURSIVE + INDEXED case.
Covers Bool, monomorphic ListNat, polymorphic List, the identity type Eq
(J eliminator), and length-indexed vectors Vec (recursive AND indexed).

The recursive+indexed case is the subtle one: a recursive field may sit at a
DIFFERENT index than the constructor's output (Vec's tail xs : Vec A n inside
vcons : ... -> Vec A (succ n)).  So each Fld carries rec_index_vals (the index
values of that recursive occurrence), and the recursor's IH / the iota
recursive call use the FIELD's indices, not the constructor's output index.
Inductive.rec_calls() computes those concrete indices at reduction time.

Validation: regenerating Nat reproduces db.mm1's hand-written recursor type
verbatim, and List/Eq schemas match hand-built de Bruijn (see run_induct.py).
The Vec recursor type is validated end-to-end: mm0-c accepts the certified
vlength computation, which would fail if the IH index arithmetic were wrong.
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

# ---- universe polymorphism: detect free level variables in a generated type ----
_LVL_KEYWORDS = {"lz", "lS", "lmax", "limax"}

def _level_vars_in(t: T, acc: set) -> set:
    """Collect the free level-VARIABLE identifiers occurring in a db-term's ESort
    levels -- any token that is not a level keyword (lz/lS/lmax/limax) is a level
    variable.  Used to bind exactly the universe params a generated axiom mentions:
    the recursor's motive level `u` (always present) plus an inductive's own level
    params (e.g. Eq's `v` for `A : Sort v`).  A non-polymorphic inductive (Bool /
    List / Vec, whose Sorts are closed lz/lS towers) yields the empty set, so its
    axioms are emitted exactly as before."""
    if isinstance(t, ESort):
        for tok in t.lvl.replace("(", " ").replace(")", " ").split():
            if tok not in _LVL_KEYWORDS:
                acc.add(tok)
    elif isinstance(t, App):  _level_vars_in(t.f, acc); _level_vars_in(t.a, acc)
    elif isinstance(t, Lam):  _level_vars_in(t.ty, acc); _level_vars_in(t.body, acc)
    elif isinstance(t, EPi):  _level_vars_in(t.dom, acc); _level_vars_in(t.body, acc)
    return acc

def _lvl_binder(t: T) -> str:
    """An MM0 `(v u: lvl)` binder list for the level vars a type mentions, or ``."""
    vs = sorted(_level_vars_in(t, set()))
    return (" (" + " ".join(vs) + ": lvl)") if vs else ""

def _eval_n(t: N, env):
    """Evaluate a (closed-over-env) named term to a db-term, resolving NVar via
    `env` (name -> db-term).  Used to compute a recursive field's concrete index
    values from concrete field values at iota-reduction time."""
    if isinstance(t, NVar):   return env[t.name]
    if isinstance(t, NConst): return Const(t.name)
    if isinstance(t, NSort):  return ESort(t.lvl)
    if isinstance(t, NApp):   return App(_eval_n(t.f, env), _eval_n(t.a, env))
    raise TypeError(t)

# ---------------- inductive spec ----------------
@dataclass(frozen=True)
class Fld:
    rec: bool                 # True = recursive occurrence of the type
    ty: object = None         # if non-rec: an N term for the field type (may
                              # reference params + earlier fields by name)
    name: str = None          # binder name; defaults to f{i} by position
    rec_index_vals: tuple = ()  # if rec AND indexed: the index values at which
                              # this recursive occurrence sits (N terms, in scope
                              # of params + earlier fields).  e.g. (NVar("n"),)
                              # for vcons's tail field  xs : Vec A n.

@dataclass(frozen=True)
class Ctor:
    name: str
    fields: tuple             # tuple[Fld]
    index_vals: tuple = ()    # tuple[N] — for an INDEXED inductive, the index
                              # values this ctor produces (in scope of params +
                              # its own fields).  () for non-indexed.

@dataclass
class Inductive:
    tycon: str                # type-former const, e.g. "tbool"
    level: str                # MM0 level the *result* Sort inhabits
    ctors: list               # list[Ctor]
    rec_name: str             # recursor const, e.g. "brec"
    params: tuple = ()        # tuple[(name, N-kind)] uniform parameters, e.g.
                              #   (("A", NSort("(lS lz)")),) for List
    indices: tuple = ()       # tuple[(name, N-kind)] index telescope (after the
                              #   params), e.g. (("b", NVar("A")),) for Eq A a
    # filled in by _build():
    tycon_type: T = None      # full type former type (Pi params, Pi indices, Sort)
    rec_type: T = None        # full recursor type
    ctor_types: dict = dfield(default_factory=dict)

    def rec_calls(self, cidx, params, cfields):
        """For constructor `cidx` applied to concrete db-term params + fields,
        return [(field_pos, [index db-terms]), ...] for each recursive field.
        The certifier uses this to build the recursor's recursive call at the
        field's own indices.  Non-indexed rec fields yield empty index lists."""
        c = self.ctors[cidx]
        fnames = _fnames(c)
        env = {pn: pv for (pn, _), pv in zip(self.params, params)}
        env.update({fnames[i]: cfields[i] for i in range(len(c.fields))})
        out = []
        for i, fl in enumerate(c.fields):
            if fl.rec:
                out.append((i, [_eval_n(iv, env) for iv in fl.rec_index_vals]))
        return out

# ---------------- schema construction ----------------
# Schemas are built with parameter binders in scope.  `_tyapp` is the inductive
# applied to params only; `_rec_field_ty` is the type of a recursive field,
# which for an indexed inductive carries that field's own index values.
def _fnames(c):
    return [fl.name or f"f{i}" for i, fl in enumerate(c.fields)]

def _tyapp(ind):
    return napps(NConst(ind.tycon), [NVar(n) for n, _ in ind.params])

def _rec_field_ty(ind, fl):
    # tycon @ params @ (this recursive field's index values)
    return napps(NConst(ind.tycon),
                 [NVar(n) for n, _ in ind.params] + list(fl.rec_index_vals))

def _tyapp_idx(ind):
    """tycon applied to params AND the index binder names (for C's kind/tail)."""
    return napps(NConst(ind.tycon),
                 [NVar(n) for n, _ in ind.params] + [NVar(n) for n, _ in ind.indices])

def _wrap_binders(binders, body):
    for name, kind in reversed(binders):
        body = NPi(name, kind, body)
    return body

def _ctor_type_N(ind, c):
    # result type: tycon @ params @ (this ctor's index values)
    fnames = _fnames(c)
    body = napps(NConst(ind.tycon),
                 [NVar(n) for n, _ in ind.params] + list(c.index_vals))
    for i in reversed(range(len(c.fields))):       # named field binders
        fl = c.fields[i]
        fty = _rec_field_ty(ind, fl) if fl.rec else fl.ty
        body = NPi(fnames[i], fty, body)
    return _wrap_binders(ind.params, body)

def _minor_N(ind, c):
    """C (c.index_vals) (c params fields)  wrapped by IHs then fields.
    An IH for a recursive field uses THAT field's index values (e.g. n for
    vcons's tail), not the constructor's output index (succ n)."""
    fnames = _fnames(c)
    capp = napps(NConst(c.name),
                 [NVar(n) for n, _ in ind.params] + [NVar(n) for n in fnames])
    body = napps(NVar("C"), list(c.index_vals) + [capp])
    for i in reversed(range(len(c.fields))):       # IHs, innermost-first
        fl = c.fields[i]
        if fl.rec:
            ih = napps(NVar("C"), list(fl.rec_index_vals) + [NVar(fnames[i])])
            body = NPi("_", ih, body)
    for i in reversed(range(len(c.fields))):       # field binders
        fl = c.fields[i]
        fty = _rec_field_ty(ind, fl) if fl.rec else fl.ty
        body = NPi(fnames[i], fty, body)
    return body

def _rec_C_kind(ind):
    # C : Pi indices, (tycon params indices) -> Sort u
    return _wrap_binders(ind.indices,
                         NPi("_", _tyapp_idx(ind), NSort(ind.level_u)))

def _rec_tail(ind):
    # Pi indices, Pi x:(tycon params indices), C indices x
    inner = NPi("x", _tyapp_idx(ind),
                napps(NVar("C"), [NVar(n) for n, _ in ind.indices] + [NVar("x")]))
    return _wrap_binders(ind.indices, inner)

def _rec_type_N(ind):
    body = _rec_tail(ind)
    for c in reversed(ind.ctors):
        body = NPi("_", _minor_N(ind, c), body)
    body = NPi("C", _rec_C_kind(ind), body)
    return _wrap_binders(ind.params, body)

def _tycon_type_N(ind):
    return _wrap_binders(ind.params, _wrap_binders(ind.indices, NSort(ind.level)))

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
    # typing -- each axiom binds exactly the universe params its type mentions
    # (none for a monomorphic inductive; the motive level `u` for every recursor;
    # plus the inductive's own level params for a universe-polymorphic one, e.g. Eq).
    L.append(f"axiom ht_{ind.tycon} (g: ctx){_lvl_binder(ind.tycon_type)}: "
             f"$ ht g {ind.tycon} {pp(ind.tycon_type)} $;")
    for c in ind.ctors:
        L.append(f"axiom ht_{c.name} (g: ctx){_lvl_binder(ind.ctor_types[c.name])}: "
                 f"$ ht g {c.name} {pp(ind.ctor_types[c.name])} $;")
    L.append(f"axiom ht_{ind.rec_name} (g: ctx){_lvl_binder(ind.rec_type)}: "
             f"$ ht g {ind.rec_name} {pp(ind.rec_type)} $;")
    # gated iota, one per constructor
    L.append(_iota_axioms(ind))
    return "\n".join(L) + "\n"

# render an N-expression to MM0 surface syntax, mapping spec names -> axiom vars
def _render(n, namemap):
    if isinstance(n, NVar):   return namemap[n.name]
    if isinstance(n, NConst): return n.name
    if isinstance(n, NSort):  return f"(esort {n.lvl})"
    if isinstance(n, NApp):   return f"({_render(n.f, namemap)} @ {_render(n.a, namemap)})"
    raise TypeError(f"_render: unsupported index expr {n}")

def _iota_axioms(ind) -> str:
    k = len(ind.ctors)
    pvars = [f"p{i}" for i in range(len(ind.params))]
    pmap = {name: pvars[i] for i, (name, _) in enumerate(ind.params)}
    mvars = [f"m{i}" for i in range(k)]
    rec_head = "(" + " @ ".join([ind.rec_name] + pvars + ["C"] + mvars) + ")"
    out = []
    for j, c in enumerate(ind.ctors):
        fvars = [f"a{i}" for i in range(len(c.fields))]
        # map this ctor's field names to axiom field vars (a0,a1,...)
        nmap = dict(pmap)
        nmap.update({fn: fvars[i] for i, fn in enumerate(_fnames(c))})
        idxstrs = [_render(iv, nmap) for iv in c.index_vals]
        ctor_args = pvars + fvars
        capp = "(" + " @ ".join([c.name] + ctor_args) + ")" if ctor_args else c.name
        # the type former applied to params + this ctor's index values
        tyargs = pvars + idxstrs
        tyapp = "(" + " @ ".join([ind.tycon] + tyargs) + ")" if tyargs else ind.tycon
        # LHS recursor application: rec_head @ <ctor index vals> @ (ctor ...)
        lhs = "(" + " @ ".join([rec_head] + idxstrs + [capp]) + ")"
        # contractum: m_j @ fields @ (rec_head @ <rec field indices> @ f_r)
        rhs = mvars[j]
        for fv in fvars:
            rhs = f"({rhs} @ {fv})"
        for i, fl in enumerate(c.fields):
            if fl.rec:
                ridx = [_render(iv, nmap) for iv in fl.rec_index_vals]
                reccall = "(" + " @ ".join([rec_head] + ridx + [fvars[i]]) + ")"
                rhs = f"({rhs} @ {reccall})"
        binders = " ".join(pvars + ["C"] + mvars + fvars + ["mt"])
        out.append(
            f"axiom deq_iota_{c.name} (g: ctx) ({binders}: expr):\n"
            f"  $ ht g {rec_head} mt $ >\n"
            f"  $ ht g {capp} {tyapp} $ >\n"
            f"  $ deq g {lhs} {rhs} $;")
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

# Identity type / equality.  Indexed: params (A : Sort1) (a : A); index (b : A).
#   teq   : Pi A:Sort1, Pi a:A, Pi b:A, Prop          (Eq is a Prop -- Sort 0!)
#   refl  : Pi A:Sort1, Pi a:A, teq A a a              (index b := a)
#   eqrec : Pi A, Pi a, Pi C:(Pi b:A, teq A a b -> Sort u),
#             C a (refl A a) -> Pi b:A, Pi h:teq A a b, C b h    (the J rule)
# The result Sort is `lz` (Prop), matching the kernel `Eq.{u} : .. -> Prop`; an
# earlier `(lS lz)` mis-stated Eq as Sort 1, which clashed when an `Eq` value sat
# in a Prop-expecting slot (Decidable p, p : Prop) -- e.g. bool_dec_eq.lean.
# UNIVERSE-POLYMORPHIC: A : Sort v for a level VARIABLE v (was the monomorphic
# Sort 1).  generate() auto-detects `v` in teq/refl_eq/eqrec and binds it on each
# typing axiom (ht_teq (g)(v: lvl) ..., eqrec (g)(u v: lvl) ... with u the motive
# level), so MM0 unifies v at each use site -- `Eq.{1}` and a level-generic
# `Eq.{u}` (e.g. my_eq_symm.{u}) both typecheck against the SAME axioms, with no
# trusted-base change beyond the level binder.  This is the dual, at the inductive
# level, of how ht_rec is universe-poly in its motive.
EQ = Inductive("teq", "lz", [
    Ctor("refl_eq", (), index_vals=(NVar("a"),)),
], "eqrec",
    params=(("A", NSort("v")), ("a", NVar("A"))),
    indices=(("b", NVar("A")),))

# Length-indexed vectors -- RECURSIVE *and* INDEXED.  param A:Sort1; index n:Nat.
#   vnil  : Vec A 0
#   vcons : Pi n:Nat, Pi a:A, Pi xs:(Vec A n), Vec A (succ n)
# The tail field xs lives at index n, but the ctor produces index (succ n) --
# so the IH / recursive call use n, not (succ n).
VEC = Inductive("tvec", "(lS lz)", [
    Ctor("vnil", (), index_vals=(NConst("tzero"),)),
    Ctor("vcons", (
        Fld(rec=False, ty=NAT_T,      name="n"),
        Fld(rec=False, ty=NVar("A"),  name="a"),
        Fld(rec=True,  rec_index_vals=(NVar("n"),)),
    ), index_vals=(NApp(NConst("tsucc"), NVar("n")),)),
], "vrec",
    params=(("A", NSort("(lS lz)")),),
    indices=(("n", NAT_T),))
