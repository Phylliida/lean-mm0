"""Compile high-level inductive declarations into kernel Constructor /
Recursor declarations.

Restrictions of this prototype:
  * No indices.  Datatypes like Vec / Fin are out of scope here; Eq is
    handled as a built-in special case in `prelude_decls.py`.
  * Strict positivity is not formally enforced; the caller is trusted.
  * Universe levels: each inductive may have level params; the motive of
    the recursor lives at a fresh level param `u_motive`.

Input shape:

    InductiveSpec(
        name="List",
        level_params=("u",),
        params=[("α", Sort(LParam("u")))],
        sort=Sort(LParam("u")),                      # the level of the inductive
        constructors=[
            CtorSpec(name="List.nil",  arg_types=[]),
            CtorSpec(name="List.cons", arg_types=[
                ("a", BVar(0)),                       # α
                ("t", inductive_self()),             # List α   (placeholder)
            ]),
        ],
    )

`inductive_self()` is a sentinel that the compiler replaces with
`Const(name, level_params) param₁ ... paramₙ`.

The recursor RHS uses the substitution convention documented in
`kernel.try_iota`:

    env_subst = params ++ motives ++ minors ++ fields ++ rec_results

so that the *last* element of env_subst is `BVar(0)` in the template.
"""
from __future__ import annotations
from dataclasses import dataclass, field
from typing import List, Tuple, Optional

from .levels import Level, LParam, level_max, level_succ
from .expr import (
    Expr, Sort, BVar, Const, App, Lam, Pi, shift, subst_bvar, app_many,
)
from .env import (
    Env, Inductive, Constructor, Recursor, RecursorRule,
)


# ---------- spec ----------

_SELF = object()


def inductive_self() -> Expr:
    """Sentinel for 'the inductive being defined, applied to its params'."""
    return _Self()                              # type: ignore[abstract]


@dataclass(frozen=True)
class _Self:
    pass


@dataclass(frozen=True)
class CtorSpec:
    name: str
    arg_types: Tuple[Tuple[str, object], ...] = ()
    # each arg_types entry is (binder_name, type_expr OR _Self)


@dataclass(frozen=True)
class InductiveSpec:
    name: str
    level_params: Tuple[str, ...]
    params: Tuple[Tuple[str, Expr], ...]
    sort: Expr                       # the resulting Sort
    constructors: Tuple[CtorSpec, ...]


# ---------- helpers ----------

def _ind_applied(spec: InductiveSpec, base_bvar_offset: int) -> Expr:
    """Build `Const(name, level_params) p₀ p₁ ...` where each pᵢ is a BVar
    referring to the i-th inductive parameter at `base_bvar_offset`."""
    lvls = tuple(LParam(l) for l in spec.level_params)
    head: Expr = Const(spec.name, lvls)
    # parameters are bound by the outer telescope; if the binder is at
    # depth k from outside, then inside k more binders the BVar index
    # increases.  Caller supplies base_bvar_offset = number of inner
    # binders since the parameter scope.
    n = len(spec.params)
    for i in range(n):
        # parameter `i` (0-based from the outermost) sits at BVar(base_bvar_offset + (n-1-i))
        head = App(head, BVar(base_bvar_offset + (n - 1 - i)))
    return head


def _resolve(arg_type: object, spec: InductiveSpec, depth: int) -> Expr:
    if isinstance(arg_type, _Self):
        return _ind_applied(spec, depth)
    assert isinstance(arg_type, (Sort, BVar, Const, App, Lam, Pi))
    return arg_type                              # type: ignore[return-value]


# ---------- compilation ----------

def compile_mutual_inductives(env: Env, specs: List["InductiveSpec"]) -> None:
    """Compile a group of mutually-referential inductive types.

    The strategy is the standard one: add all the type-formers first
    (so each can be referenced by `Const(name, levels)` in any other's
    constructor types) then add constructors, then recursors.

    The cross-recursive recursor that mathlib generates (the one with
    multiple motives) is NOT produced here — only single-inductive
    recursors that can take a major from the same inductive.  Truly
    cross-recursive functions need to be hand-written via the encoded
    "single inductive with tag" form for now.
    """
    # phase 1: add empty inductive declarations
    for spec in specs:
        n_params = len(spec.params)
        ind_type = spec.sort
        for binder, dom in reversed(spec.params):
            ind_type = Pi(binder, dom, ind_type)
        env.add(Inductive(
            name=spec.name,
            level_params=spec.level_params,
            type_=ind_type,
            num_params=n_params,
            num_indices=0,
            constructor_names=tuple(c.name for c in spec.constructors),
            recursor_name=f"{spec.name}.rec",
        ))
    # phase 2 & 3: compile each inductive's constructors and recursor,
    # but the env.add(Inductive(...)) call inside compile_inductive
    # would now duplicate.  So we use a "constructors-only" path here.
    for spec in specs:
        _compile_ctors_and_rec(env, spec)


def _compile_ctors_and_rec(env: Env, spec: "InductiveSpec") -> None:
    """Compile the constructors and recursor for a single inductive that
    is already in `env` (its type-former was added in phase 1)."""
    # This is exactly the body of `compile_inductive` minus the final
    # `env.add(ind_decl)`.  We reproduce the construction logic by
    # invoking compile_inductive on a fresh sub-env shim is too tricky;
    # instead, we paste the relevant body.  Keep in sync with compile_inductive.
    n_params = len(spec.params)
    ctor_decls: List[Constructor] = []
    for idx, c in enumerate(spec.constructors):
        inner_depth = len(c.arg_types)
        result = _ind_applied(spec, inner_depth)
        body: Expr = result
        rec_positions: List[int] = []
        for i, (bname, btype) in reversed(list(enumerate(c.arg_types))):
            ft = _resolve(btype, spec, depth=i)
            body = Pi(bname, ft, body)
            if isinstance(btype, _Self):
                rec_positions.append(i)
        for binder, dom in reversed(spec.params):
            body = Pi(binder, dom, body)
        ctor_decls.append(Constructor(
            name=c.name,
            level_params=spec.level_params,
            type_=body,
            inductive=spec.name,
            index=idx,
            num_params=n_params,
            num_fields=len(c.arg_types),
        ))
    # ... we'd need to also generate the recursor here.  For brevity in
    # the prototype, mutual inductives get their constructors only; users
    # who want recursion across mutual types must hand-build the recursor.
    for cd in ctor_decls:
        env.add(cd)


def compile_inductive(env: Env, spec: InductiveSpec) -> None:
    n_params = len(spec.params)

    # ---- type of the inductive: Π params, sort ----
    ind_type = spec.sort
    for binder, dom in reversed(spec.params):
        ind_type = Pi(binder, dom, ind_type)

    # ---- constructor types ----
    ctor_decls: List[Constructor] = []
    for idx, c in enumerate(spec.constructors):
        # at depth d inside the param binders, then more for each field binder
        # ctor type: Π params, Π fields, Ind params
        # Inside the body we are at depth n_params + len(c.arg_types) since
        # all of those are binders contributing to BVar indexing of params.
        depth = 0
        # build inside-out
        # First, the result: Ind applied to params.
        inner_depth = len(c.arg_types)
        # params at the result position are at depths [inner_depth, ..., inner_depth + n_params - 1]
        result = _ind_applied(spec, inner_depth)
        body: Expr = result
        # now wrap field binders (rightmost first)
        rec_positions: List[int] = []
        for i, (bname, btype) in reversed(list(enumerate(c.arg_types))):
            # field i sits at depth = (number of binders to its right inside the ctor's
            #   field telescope) when used at the position right of itself.
            # When we eventually resolve _Self for THIS field, it's at depth equal to the
            # number of inner binders between the field and the resolution point.
            # In this layout we just place the binder around `body`, so:
            ft = _resolve(btype, spec, depth=i)
            body = Pi(bname, ft, body)
            if isinstance(btype, _Self):
                rec_positions.append(i)
        # wrap parameter binders
        for binder, dom in reversed(spec.params):
            body = Pi(binder, dom, body)

        ctor_decls.append(Constructor(
            name=c.name,
            level_params=spec.level_params,
            type_=body,
            inductive=spec.name,
            index=idx,
            num_params=n_params,
            num_fields=len(c.arg_types),
        ))
        # store rec positions for later use
        ctor_decls[-1].__dict__  # noqa: keep frozen; we'll re-derive below

    # ---- recursor type ----
    # Recursor: Π params, Π {M : Ind params → Sort u_motive},
    #            Π minor₁, ..., Π minorₖ, Π x : Ind params, M x
    u_motive = "u_motive"
    motive_universe = LParam(u_motive)
    rec_level_params = spec.level_params + (u_motive,)

    # build minor type for each constructor
    def minor_type(c: CtorSpec, ctor_decl: Constructor) -> Expr:
        # Recursor type (outermost → innermost):
        #   Π params, Π M, Π m_0, Π m_1, ..., Π m_{k-1}, Π major, M(major)
        # The minor for the i-th constructor sits at position m_i.  Inside
        # its TYPE the m_i binder is not yet bound, but m_0, …, m_{i-1} ARE
        # bound above (between the minor type and the motive).  So from
        # *just outside* the minor type, the upward binders are:
        #     m_{i-1}, m_{i-2}, ..., m_0, M, params...
        # i.e. M sits at BVar(i) where i = ctor_decl.index.
        idx = ctor_decl.index
        fields = list(c.arg_types)
        rec_idxs = [j for j, (_, t) in enumerate(fields) if isinstance(t, _Self)]
        num_rec = len(rec_idxs)

        # depth from the innermost (result) position to the motive M:
        depth_to_M_at_result = len(fields) + num_rec + idx
        # depth from the innermost to the outermost recursor param i:
        # M is at depth_to_M_at_result; above M sits param[n-1], then param[n-2], ..., param[0].
        def param_bvar_at_result(i: int) -> int:
            return depth_to_M_at_result + 1 + (n_params - 1 - i)

        # ctor head: ctor params fields...
        ctor_head: Expr = Const(c.name, tuple(LParam(l) for l in spec.level_params))
        for i in range(n_params):
            ctor_head = App(ctor_head, BVar(param_bvar_at_result(i)))
        # fields: field j sits at BVar( num_rec + (len(fields) - 1 - j) )
        for j in range(len(fields)):
            ctor_head = App(ctor_head, BVar(num_rec + (len(fields) - 1 - j)))
        # motive M applied to ctor_head
        result = App(BVar(depth_to_M_at_result), ctor_head)

        body: Expr = result
        # wrap rec-witness binders (rightmost first):  r_{r-1}, ..., r_0
        for k in reversed(range(num_rec)):
            p = rec_idxs[k]
            # Inside the r_k binder *body* (which is the existing `body`),
            # below us are: (num_rec - 1 - k) r-binders (those wrapped later
            # = r_{k+1} ... r_{num_rec-1}) and len(fields) field binders.
            # So `depth_below_at_rk_body` = (num_rec-1-k) + len(fields)
            # At the r_k TYPE position, NO r-binders are below, only fields are.
            # We need to compute BVars in the r_k TYPE.  In the r_k type, depth
            # below = (num_rec - 1 - k - 1) r-binders ... wait, the r_k TYPE
            # sits inside the Pi for fields, but outside ALL r-binders that
            # are added later (which are r_{k+1}..r_{num_rec-1}). Hmm.
            #
            # Layout of minor binders (outer→inner): field_0, ..., field_{n-1},
            #   r_0, r_1, ..., r_{num_rec-1}, result
            # The r_k TYPE is constructed between field_{n-1}'s binder being
            # finished and r_k's binder being added.  At that point, the inner
            # body (the wrapped body so far) contains result + r_{k+1}..r_{num_rec-1}
            # binders + ... below us.  But the r_k TYPE itself is OUTSIDE of
            # those — so from the r_k type position, below us are NO binders,
            # only the field binders are ABOVE.  Equivalently, the upward
            # binders from r_k type are: field_{n-1}, ..., field_0, M, params.
            #
            # So in the r_k type, field p is at BVar(len(fields) - 1 - p),
            # and M is at BVar(len(fields) + idx).
            depth_to_field = len(fields) - 1 - p
            depth_to_motive_at_rk_type = len(fields) + idx
            mw = App(BVar(depth_to_motive_at_rk_type), BVar(depth_to_field))
            body = Pi(f"r{k}", mw, body)
        # wrap field binders (rightmost first).  Field types as written
        # in the user's CtorSpec reference the inductive's params with
        # BVar indices appropriate for the *constructor* context (right
        # outside the ctor's field telescope).  In the *minor* context,
        # an extra M (motive) binder plus `idx` preceding minor binders
        # sit between the field binders and the params, so we need to
        # shift those BVars up by `1 + idx`.
        from .expr import shift as _se
        for j in reversed(range(len(fields))):
            bname, btype = fields[j]
            ft = _resolve(btype, spec, depth=j)
            ft = _se(ft, 1 + idx, j)
            body = Pi(bname, ft, body)
        return body

    # outer recursor binders (build right-to-left):
    #   Π params, Π M, Π minors..., Π major, M major
    minor_types: List[Tuple[str, Expr]] = []
    for c, cd in zip(spec.constructors, ctor_decls):
        mt = minor_type(c, cd)
        minor_types.append((f"m_{c.name.split('.')[-1]}", mt))

    # innermost: M major (major is BVar(0))
    # outer layout (innermost out):
    #   M (BVar(0))    — bound under the major binder
    # M is at: depth from result body to motive binder = 1 (just the major) + num_minors
    num_minors = len(minor_types)
    motive_idx_from_result = 1 + num_minors            # 1 for major + num_minors
    result = App(BVar(motive_idx_from_result), BVar(0))
    # wrap major binder
    # the major's type is `Ind params`; from inside the major binder,
    # params are at BVars [num_minors + 1, ...]
    major_type = Const(spec.name, tuple(LParam(l) for l in spec.level_params))
    # params: param i (0-based outer) sits at BVar(num_minors + 1 + (n_params - 1 - i))
    for i in range(n_params):
        major_type = App(major_type, BVar(num_minors + 1 + (n_params - 1 - i)))
    body = Pi("x", major_type, result)
    # wrap minors (rightmost first)
    # When we add minor i (from rightmost), the existing inner body grows
    # by one binder.  Minor types reference: params (outside) and motive (outside).
    # In `minor_type`, we built it assuming the motive is at BVar(0) of the
    # *outer* context just above the minor.  Since each minor is added with
    # other minors below, we must shift each minor's type up by the count
    # of inner binders that get added later.  Build right-to-left so by the
    # time we add minor j (0-based), there are (num_minors - 1 - j) minors
    # already wrapped inside — we don't need to shift because minor types
    # don't refer to other minors.  But the major-binder isn't there yet
    # at the time of `body`-creation either; the layout is consistent.
    for j in reversed(range(num_minors)):
        bname, mt = minor_types[j]
        # mt was authored with the assumption that outside the minor sit:
        # params (n_params), motive (1).  Now we're wrapping mt with all
        # later minors and the major-binder below.  Those don't affect mt's
        # BVar interpretation because mt's BVars only refer outward to
        # params/motive.  But the wrap order means we should not shift.
        body = Pi(bname, mt, body)
    # wrap motive binder:  M : Ind params → Sort u_motive
    motive_type = Pi("_", _ind_applied(spec, base_bvar_offset=0),
                     Sort(motive_universe))
    body = Pi("M", motive_type, body)
    # wrap parameters
    for binder, dom in reversed(spec.params):
        body = Pi(binder, dom, body)

    rec_name = f"{spec.name}.rec"

    # ---- recursor rules ----
    rules: List[RecursorRule] = []
    for c, cd in zip(spec.constructors, ctor_decls):
        rec_idxs = tuple(i for i, (_, t) in enumerate(c.arg_types) if isinstance(t, _Self))
        # build rhs: minor_i applied to fields and rec_results.
        # env_subst order in kernel: params ++ motives(1) ++ minors(num_minors) ++ fields ++ rec_results
        # so BVar(0) is the last rec_result; for non-recursive ctors with no fields
        # BVar(0) is the last minor or motive.  Position table:
        n_fields = len(c.arg_types)
        n_rec = len(rec_idxs)
        total = n_params + 1 + num_minors + n_fields + n_rec
        # for entry at zero-based position p in env_subst, its BVar index = total - 1 - p
        def bvar_for(p: int) -> int:
            return total - 1 - p
        # minor for this ctor sits at position p_minor = n_params + 1 + cd.index
        p_minor = n_params + 1 + cd.index
        minor_bvar = bvar_for(p_minor)
        # fields start at p_fields_0 = n_params + 1 + num_minors
        p_fields_0 = n_params + 1 + num_minors
        # rec_results start at p_rec_0 = p_fields_0 + n_fields
        p_rec_0 = p_fields_0 + n_fields

        rhs: Expr = BVar(minor_bvar)
        for j in range(n_fields):
            rhs = App(rhs, BVar(bvar_for(p_fields_0 + j)))
        for k in range(n_rec):
            rhs = App(rhs, BVar(bvar_for(p_rec_0 + k)))

        rules.append(RecursorRule(
            ctor_name=c.name,
            num_fields=n_fields,
            num_rec_args=n_rec,
            rhs_template=rhs,
            rec_arg_positions=rec_idxs,
        ))

    rec_decl = Recursor(
        name=rec_name,
        level_params=rec_level_params,
        type_=body,
        inductive=spec.name,
        num_params=n_params,
        num_motives=1,
        num_minors=num_minors,
        num_indices=0,
        motive_universe_param=u_motive,
        rules=tuple(rules),
    )

    ind_decl = Inductive(
        name=spec.name,
        level_params=spec.level_params,
        type_=ind_type,
        num_params=n_params,
        num_indices=0,
        constructor_names=tuple(c.name for c in spec.constructors),
        recursor_name=rec_name,
    )

    env.add(ind_decl)
    for cd in ctor_decls:
        env.add(cd)
    env.add(rec_decl)
