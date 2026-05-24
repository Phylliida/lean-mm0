"""A minimal Lean-style elaborator.

Pieces implemented in this iteration:
  1. Metavariables (Meta) live in Expr; MetaContext tracks types + assignments.
  2. First-order unification with δ-fallback, structural decomposition,
     Meta-assignment with occurs check.
  3. Implicit-argument insertion: at every App, if the function's type
     starts with `Π {x : T}, U`, a fresh meta is inserted in place of x.
  4. After elaboration, every Meta must be solved — `instantiate` walks
     the term and substitutes the assignments; any leftover Meta is an
     error.

Out of scope for this iteration:
  - Universe-level metas (we still require explicit `.{u}` annotations)
  - Higher-order pattern unification (Miller fragment)
  - Type-class instance synthesis
  - Coercions
  - Pre-elaboration (numeric literal `OfNat`-style coercion)

The kernel never sees Metas: `instantiate_fully` is called before
handing the term to `Kernel.add_definition`.
"""
from __future__ import annotations
from dataclasses import dataclass, field
from typing import Dict, Optional, Tuple, List

from .levels import (
    Level, LZero, LSucc, LMax, LIMax, LParam, LMeta,
    equiv as level_equiv, normalize as level_normalize, show as show_level,
    subst as level_subst,
)
from .expr import (
    Expr, Sort, BVar, FVar, Const, App, Lam, Pi, Let, Meta, Explicit, By,
    shift, subst_bvar, open_, close, inst_levels, show as show_expr,
)
from .env import Env, Definition, Axiom, Constructor, Recursor, Inductive
from .kernel import Kernel, LocalCtx, TypeError_


# ---------------- meta context ----------------

@dataclass
class MetaInfo:
    type_: Expr
    assignment: Optional[Expr] = None


class MetaContext:
    def __init__(self) -> None:
        self.metas: Dict[int, MetaInfo] = {}
        self.level_metas: Dict[int, Optional[Level]] = {}
        self._next_id = 0
        self._next_lid = 0

    def fresh(self, type_: Expr) -> Meta:
        i = self._next_id
        self._next_id += 1
        self.metas[i] = MetaInfo(type_=type_)
        return Meta(i)

    def fresh_level(self) -> Level:
        i = self._next_lid
        self._next_lid += 1
        self.level_metas[i] = None
        return LMeta(i)

    def assign(self, id_: int, value: Expr) -> None:
        info = self.metas[id_]
        assert info.assignment is None, f"meta ?m{id_} already assigned"
        info.assignment = value

    def assign_level(self, id_: int, value: Level) -> None:
        assert self.level_metas[id_] is None, f"level meta ?u{id_} already assigned"
        self.level_metas[id_] = value

    def get(self, id_: int) -> Optional[Expr]:
        return self.metas[id_].assignment

    def get_level(self, id_: int) -> Optional[Level]:
        return self.level_metas.get(id_)

    def get_type(self, id_: int) -> Expr:
        return self.metas[id_].type_

    def instantiate_level(self, l: Level) -> Level:
        """Recursively replace assigned LMetas with their values."""
        if isinstance(l, LMeta):
            v = self.get_level(l.id)
            if v is None:
                return l
            return self.instantiate_level(v)
        if isinstance(l, (LZero, LParam)):
            return l
        if isinstance(l, LSucc):
            return LSucc(self.instantiate_level(l.arg))
        if isinstance(l, LMax):
            return LMax(self.instantiate_level(l.a), self.instantiate_level(l.b))
        if isinstance(l, LIMax):
            return LIMax(self.instantiate_level(l.a), self.instantiate_level(l.b))
        raise TypeError(l)

    def instantiate(self, e: Expr) -> Expr:
        """Walk e, replacing every assigned Meta and LMeta with its
        (recursively instantiated) assignment.  Unassigned metas are
        left intact."""
        if isinstance(e, Meta):
            v = self.get(e.id)
            if v is None:
                return e
            return self.instantiate(v)
        if isinstance(e, Explicit):
            return self.instantiate(e.inner)
        if isinstance(e, Sort):
            return Sort(self.instantiate_level(e.level))
        if isinstance(e, Const):
            return Const(e.name, tuple(self.instantiate_level(l) for l in e.levels))
        if isinstance(e, (BVar, FVar)):
            return e
        if isinstance(e, App):
            return App(self.instantiate(e.fn), self.instantiate(e.arg))
        if isinstance(e, Lam):
            return Lam(e.binder, self.instantiate(e.dom),
                       self.instantiate(e.body))
        if isinstance(e, Pi):
            return Pi(e.binder, self.instantiate(e.dom),
                      self.instantiate(e.body), e.implicit, e.inst_implicit)
        if isinstance(e, Let):
            return Let(e.binder, self.instantiate(e.type_),
                       self.instantiate(e.value),
                       self.instantiate(e.body))
        raise TypeError(e)

    def instantiate_fully(self, e: Expr) -> Expr:
        """Like `instantiate`, but raises if any Meta / LMeta remains."""
        out = self.instantiate(e)
        unsolved_e = _collect_metas(out)
        unsolved_l = _collect_level_metas(out)
        if unsolved_e or unsolved_l:
            parts = []
            if unsolved_e:
                parts.append(f"expression metas: ?m{','.join(str(i) for i in sorted(unsolved_e))}")
            if unsolved_l:
                parts.append(f"level metas: ?u{','.join(str(i) for i in sorted(unsolved_l))}")
            raise ElabError(
                f"unsolved metavariables in {show_expr(out)}: " + "; ".join(parts))
        return out


def _collect_metas(e: Expr) -> set:
    if isinstance(e, Meta):
        return {e.id}
    if isinstance(e, (Sort, BVar, FVar, Const)):
        return set()
    if isinstance(e, App):
        return _collect_metas(e.fn) | _collect_metas(e.arg)
    if isinstance(e, (Lam, Pi)):
        return _collect_metas(e.dom) | _collect_metas(e.body)
    if isinstance(e, Let):
        return (_collect_metas(e.type_) | _collect_metas(e.value)
                | _collect_metas(e.body))
    return set()


def _level_metas(l: Level) -> set:
    if isinstance(l, LMeta): return {l.id}
    if isinstance(l, (LZero, LParam)): return set()
    if isinstance(l, LSucc): return _level_metas(l.arg)
    if isinstance(l, (LMax, LIMax)): return _level_metas(l.a) | _level_metas(l.b)
    return set()


def _collect_level_metas(e: Expr) -> set:
    if isinstance(e, Sort): return _level_metas(e.level)
    if isinstance(e, Const):
        s = set()
        for l in e.levels: s |= _level_metas(l)
        return s
    if isinstance(e, (BVar, FVar, Meta)): return set()
    if isinstance(e, App): return _collect_level_metas(e.fn) | _collect_level_metas(e.arg)
    if isinstance(e, (Lam, Pi)): return _collect_level_metas(e.dom) | _collect_level_metas(e.body)
    if isinstance(e, Let): return (_collect_level_metas(e.type_) | _collect_level_metas(e.value)
                                    | _collect_level_metas(e.body))
    return set()


def _occurs(meta_id: int, e: Expr) -> bool:
    if isinstance(e, Meta):
        return e.id == meta_id
    if isinstance(e, (Sort, BVar, FVar, Const)):
        return False
    if isinstance(e, App):
        return _occurs(meta_id, e.fn) or _occurs(meta_id, e.arg)
    if isinstance(e, (Lam, Pi)):
        return _occurs(meta_id, e.dom) or _occurs(meta_id, e.body)
    if isinstance(e, Let):
        return (_occurs(meta_id, e.type_) or _occurs(meta_id, e.value)
                or _occurs(meta_id, e.body))
    return False


class ElabError(Exception):
    pass


# ---------------- level unification ----------------

def unify_level(a: Level, b: Level, mctx: MetaContext) -> bool:
    """Unify two universe levels under mctx.  Handles assignment of
    LMeta and a few simple structural cases."""
    a = mctx.instantiate_level(a)
    b = mctx.instantiate_level(b)
    if isinstance(a, LMeta) and isinstance(b, LMeta) and a.id == b.id:
        return True
    if isinstance(a, LMeta):
        mctx.assign_level(a.id, b)
        return True
    if isinstance(b, LMeta):
        mctx.assign_level(b.id, a)
        return True
    # quick equality after normalisation
    if level_equiv(a, b):
        return True
    # succ peel
    if isinstance(a, LSucc) and isinstance(b, LSucc):
        return unify_level(a.arg, b.arg, mctx)
    # max/imax: structurally — limited; we don't try to invert max
    if isinstance(a, LMax) and isinstance(b, LMax):
        return (unify_level(a.a, b.a, mctx) and unify_level(a.b, b.b, mctx))
    if isinstance(a, LIMax) and isinstance(b, LIMax):
        return (unify_level(a.a, b.a, mctx) and unify_level(a.b, b.b, mctx))
    return False


# ---------------- unification ----------------

def _try_hop(a: Expr, b: Expr, ctx: LocalCtx, mctx: MetaContext,
             type_of=None) -> bool:
    """Higher-order pattern fragment + constant-motive fallback.

    Case A (Miller pattern): `?m e1 ... en` where each ei is a distinct
       FVar.  Abstract ei out of b to give `λ x1...xn. b'`.

    Case B (constant motive): args are not FVars OR are not distinct,
       BUT b doesn't reference any FVar that the spine arg could rebind.
       Then just wrap b in n dummy lambdas: `λ _:T1 ... _:Tn. b`.
    """
    args: List[Expr] = []
    head = a
    while isinstance(head, App):
        args.insert(0, mctx.instantiate(head.arg))
        head = head.fn
    head = mctx.instantiate(head)
    if not isinstance(head, Meta):
        return False
    if not args:
        return False
    if _occurs(head.id, b):
        return False

    # Case A: all args are distinct FVars
    all_fvars = all(isinstance(arg, FVar) for arg in args)
    distinct = len({arg.name for arg in args if isinstance(arg, FVar)}) == len(args)
    if all_fvars and distinct:
        fv_names = [arg.name for arg in args]
        result = mctx.instantiate(b)
        for fv_name in reversed(fv_names):
            result = close(result, fv_name)
        lam = result
        for arg in reversed(args):
            fv_ty = arg.type_                           # FVar.type_
            lam = Lam(arg.name, fv_ty, lam)
        mctx.assign(head.id, lam)
        return True

    # Case B: constant motive — only valid if b mentions no FVars that
    # could distinguish positions of the spine args.  Approximation:
    # only fire if every FVar in `b` is in `ctx.entries` (i.e. in scope
    # at the meta's creation, conservatively assumed all of ctx).
    # We also need types for the (anonymous) binders.  Use a generic
    # placeholder type — we don't actually need correctness here since
    # the body doesn't reference these binders.
    binder_types: List[Expr] = []
    for arg in args:
        if isinstance(arg, FVar):
            binder_types.append(arg.type_)
        elif type_of is not None:
            try:
                binder_types.append(type_of(arg))
            except Exception:
                return False
        else:
            return False
    result = mctx.instantiate(b)
    lam = result
    for i, ty in enumerate(reversed(binder_types)):
        lam = Lam(f"_", ty, lam)
    mctx.assign(head.id, lam)
    return True


def unify(a: Expr, b: Expr, ctx: LocalCtx, mctx: MetaContext,
          ker: Kernel,
          type_of=None) -> bool:
    """Unification with: meta-assignment + δ-fallback + Miller's
    higher-order pattern fragment.

    HOP pattern: if a (or b) is `?m e1 ... en` where each ei is a
    distinct FVar, abstract those FVars out of the other side to
    build `λ x1 ... xn. rhs'`, then assign ?m.
    """
    a = mctx.instantiate(a)
    b = mctx.instantiate(b)

    if isinstance(a, Meta) and isinstance(b, Meta) and a.id == b.id:
        return True
    if isinstance(a, Meta):
        if _occurs(a.id, b):
            return False
        mctx.assign(a.id, b)
        if type_of is not None:
            try:
                b_ty = type_of(b)
                want_ty = mctx.get_type(a.id)
                unify(want_ty, b_ty, ctx, mctx, ker, type_of)
            except Exception:
                pass
        return True
    if isinstance(b, Meta):
        if _occurs(b.id, a):
            return False
        mctx.assign(b.id, a)
        if type_of is not None:
            try:
                a_ty = type_of(a)
                want_ty = mctx.get_type(b.id)
                unify(want_ty, a_ty, ctx, mctx, ker, type_of)
            except Exception:
                pass
        return True

    # Higher-order pattern fragment: try a, then b.
    if _try_hop(a, b, ctx, mctx, type_of):
        return True
    if _try_hop(b, a, ctx, mctx, type_of):
        return True

    a_w = ker.whnf(a, ctx)
    b_w = ker.whnf(b, ctx)
    a_w = mctx.instantiate(a_w)
    b_w = mctx.instantiate(b_w)

    if isinstance(a_w, Meta) or isinstance(b_w, Meta):
        return unify(a_w, b_w, ctx, mctx, ker, type_of)

    if isinstance(a_w, Sort) and isinstance(b_w, Sort):
        return unify_level(a_w.level, b_w.level, mctx)

    if isinstance(a_w, BVar) and isinstance(b_w, BVar):
        return a_w.idx == b_w.idx

    if isinstance(a_w, FVar) and isinstance(b_w, FVar):
        return a_w.name == b_w.name

    if isinstance(a_w, Const) and isinstance(b_w, Const) and a_w.name == b_w.name:
        if len(a_w.levels) != len(b_w.levels):
            return False
        return all(unify_level(x, y, mctx) for x, y in zip(a_w.levels, b_w.levels))

    if isinstance(a_w, App) and isinstance(b_w, App):
        if not unify(a_w.fn, b_w.fn, ctx, mctx, ker, type_of):
            return False
        return unify(a_w.arg, b_w.arg, ctx, mctx, ker, type_of)

    if isinstance(a_w, Pi) and isinstance(b_w, Pi):
        if a_w.implicit != b_w.implicit:
            pass
        if not unify(a_w.dom, b_w.dom, ctx, mctx, ker, type_of):
            return False
        fv = ctx.push(a_w.binder, a_w.dom)
        try:
            return unify(open_(a_w.body, FVar(fv, a_w.dom)),
                         open_(b_w.body, FVar(fv, a_w.dom)),
                         ctx, mctx, ker, type_of)
        finally:
            ctx.pop()

    if isinstance(a_w, Lam) and isinstance(b_w, Lam):
        if not unify(a_w.dom, b_w.dom, ctx, mctx, ker, type_of):
            return False
        fv = ctx.push(a_w.binder, a_w.dom)
        try:
            return unify(open_(a_w.body, FVar(fv, a_w.dom)),
                         open_(b_w.body, FVar(fv, a_w.dom)),
                         ctx, mctx, ker, type_of)
        finally:
            ctx.pop()

    return False


# ---------------- elaboration ----------------

class Elaborator:
    """Elaborate preterms into kernel-ready terms.

    The elaborator's main job in this prototype is to walk the term and:
      * when a function whose declared type begins with implicit Π's is
        applied to user-supplied arguments, insert fresh metas in place
        of the implicit binders;
      * use the kernel to infer the type of each argument and unify it
        with the expected domain (this drives meta assignment);
      * fall back to leaving things alone when nothing is needed.

    For binder bodies we recurse, mapping `App` and resolving constants
    in-place.
    """

    def __init__(self, env: Env) -> None:
        self.env = env
        self.kernel = Kernel(env)
        self.mctx = MetaContext()

    # -- elaborate an expression in a typing context --

    def elab(self, e: Expr, expected: Optional[Expr],
             ctx: LocalCtx) -> Tuple[Expr, Expr]:
        """Elaborate `e` (optionally against `expected`).  Returns
        (elaborated_term, its_type)."""
        # Decompose into head + args so we can handle implicit insertion
        # at application sites uniformly.
        head, args = _spine(e)
        if isinstance(head, By):
            if args:
                raise ElabError("`by` cannot be applied as a function")
            if expected is None:
                raise ElabError("`by` needs an expected type")
            return self._run_tactic_by(head, expected, ctx), expected
        # `_` hole sentinel — Const("_", ()) emitted by the parser.
        # Becomes a fresh meta typed by `expected` (or a meta-of-meta type
        # if expected is unknown).
        if (isinstance(head, Const) and head.name == "_"
                and not args and not head.levels):
            if expected is None:
                ty_meta = self.mctx.fresh(Sort(self.mctx.fresh_level()))
                m = self.mctx.fresh(ty_meta)
            else:
                m = self.mctx.fresh(expected)
            return m, self.mctx.get_type(m.id)
        # Bare Lam at the head with no args and a known expected type:
        # propagate the expected's body into the Lam's body so `by` and
        # other expectation-sensitive forms can see it.
        if isinstance(head, Lam) and not args and expected is not None:
            return self._elab_lam_with_expected(head, expected, ctx)
        skip_implicits = False
        if isinstance(head, Explicit):
            skip_implicits = True
            head = head.inner
        head_e = self._elab_atom(head, ctx)
        head_ty = self._infer_elaborated(head_e, ctx)
        # Collect inst-implicit metas to synthesise AFTER all explicit
        # args are processed — by then `?α` etc. are pinned, so synth
        # picks the right instance instead of guessing.
        pending_inst_metas: List[Tuple[Meta, Expr]] = []

        for a in args:
            # whnf the head's type, instantiating metas, to expose a Pi
            head_ty = self.mctx.instantiate(head_ty)
            head_ty_w = self.kernel.whnf(head_ty, ctx)
            head_ty_w = self.mctx.instantiate(head_ty_w)

            # while the head's type starts with an implicit / inst-implicit
            # Π, insert a meta.  inst-implicit synthesis is DEFERRED until
            # after all explicit args are processed.
            while (not skip_implicits and isinstance(head_ty_w, Pi)
                   and (head_ty_w.implicit or head_ty_w.inst_implicit)):
                meta = self.mctx.fresh(head_ty_w.dom)
                head_e = App(head_e, meta)
                if head_ty_w.inst_implicit:
                    pending_inst_metas.append((meta, head_ty_w.dom))
                head_ty = subst_bvar(head_ty_w.body, 0, meta)
                head_ty = self.mctx.instantiate(head_ty)
                head_ty_w = self.kernel.whnf(head_ty, ctx)
                head_ty_w = self.mctx.instantiate(head_ty_w)

            if not isinstance(head_ty_w, Pi):
                raise ElabError(
                    f"too many arguments: head has non-Π type "
                    f"{show_expr(head_ty_w)}")

            dom = head_ty_w.dom
            arg_e, arg_ty = self.elab(a, dom, ctx)
            if not unify(arg_ty, dom, ctx, self.mctx, self.kernel,
                         type_of=lambda x: self._infer_elaborated(x, ctx)):
                # fall back to direct kernel def_eq via whnf+normalize
                if not self.kernel.def_eq(arg_ty, dom, ctx):
                    raise ElabError(
                        f"argument type mismatch:\n"
                        f"  expected {show_expr(self.mctx.instantiate(dom))}\n"
                        f"  got      {show_expr(self.mctx.instantiate(arg_ty))}")
            # If the user passed `_` for a slot whose type is a registered
            # class, queue it for instance synthesis after explicit args
            # have pinned its type.  (Without this, `@f _ _` for an inst
            # arg slot leaves a meta with no way to fill it.)
            if (isinstance(arg_e, Meta)
                    and self.mctx.get(arg_e.id) is None):
                dom_w = self.kernel.whnf(self.mctx.instantiate(dom), ctx)
                dom_head, _ = _spine(dom_w)
                if (isinstance(dom_head, Const)
                        and self.env.instances_of(dom_head.name)):
                    pending_inst_metas.append((arg_e, dom))
            head_e = App(head_e, arg_e)
            head_ty = subst_bvar(head_ty_w.body, 0, arg_e)

        # After consuming all user args, if the expected type was given
        # and the head's type still starts with implicit Π's whose values
        # we can leave for the caller to determine — postpone (don't fill
        # them).  This handles things like `id_poly` used as a function
        # value: don't eagerly insert metas if no arg is being applied.
        # If `expected` is given and unifies, great.
        # All explicit args processed.  Now synthesise any inst-implicit
        # metas we deferred — their types are concrete by now.
        for meta, dom in pending_inst_metas:
            if self.mctx.get(meta.id) is not None:
                continue                                   # already solved by unif
            goal = self.mctx.instantiate(dom)
            sub = self._synthesize(goal, ctx)
            if sub is None:
                raise ElabError(
                    f"failed to synthesize instance for "
                    f"{show_expr(self.mctx.instantiate(goal))}")
            self.mctx.assign(meta.id, sub)

        if expected is not None:
            if not unify(head_ty, expected, ctx, self.mctx, self.kernel,
                         type_of=lambda x: self._infer_elaborated(x, ctx)):
                if not self.kernel.def_eq(head_ty, expected, ctx):
                    raise ElabError(
                        f"type mismatch in elaboration:\n"
                        f"  expected {show_expr(self.mctx.instantiate(expected))}\n"
                        f"  got      {show_expr(self.mctx.instantiate(head_ty))}")
        return head_e, head_ty

    # -- atoms --

    def _elab_atom(self, e: Expr, ctx: LocalCtx) -> Expr:
        if isinstance(e, Const):
            # auto-instantiate level params with fresh metas if the user
            # omitted the `.{...}` annotation
            if not e.levels and self.env.has(e.name):
                decl = self.env.get(e.name)
                lps = getattr(decl, "level_params", ())
                if lps:
                    return Const(e.name, tuple(self.mctx.fresh_level() for _ in lps))
            return e
        if isinstance(e, (Sort, BVar, FVar, Meta)):
            return e
        if isinstance(e, Lam):
            dom_resolved = _resolve_bvars(e.dom, ctx)
            fv = ctx.push(e.binder, dom_resolved)
            try:
                body_open = open_(e.body, FVar(fv, dom_resolved))
                body_e, _ = self.elab(body_open, None, ctx)
                body_e = self.mctx.instantiate(body_e)
                return Lam(e.binder, dom_resolved, close(body_e, fv))
            finally:
                ctx.pop()
        if isinstance(e, Pi):
            dom_resolved = _resolve_bvars(e.dom, ctx)
            fv = ctx.push(e.binder, dom_resolved)
            try:
                body_open = open_(e.body, FVar(fv, dom_resolved))
                body_e, _ = self.elab(body_open, None, ctx)
                body_e = self.mctx.instantiate(body_e)
                return Pi(e.binder, dom_resolved, close(body_e, fv),
                          e.implicit, e.inst_implicit)
            finally:
                ctx.pop()
        if isinstance(e, Let):
            type_resolved = _resolve_bvars(e.type_, ctx)
            value_resolved = _resolve_bvars(e.value, ctx)
            fv = ctx.push(e.binder, type_resolved, value_resolved)
            try:
                body_open = open_(e.body, FVar(fv, type_resolved))
                body_e, _ = self.elab(body_open, None, ctx)
                body_e = self.mctx.instantiate(body_e)
                return Let(e.binder, type_resolved, value_resolved,
                           close(body_e, fv))
            finally:
                ctx.pop()
        if isinstance(e, App):
            # shouldn't normally happen — _spine handles App.
            head, args = _spine(e)
            head_e = self._elab_atom(head, ctx)
            for a in args:
                arg_e = self._elab_atom(a, ctx)
                head_e = App(head_e, arg_e)
            return head_e
        raise TypeError(e)

    def _infer_elaborated(self, e: Expr, ctx: LocalCtx) -> Expr:
        """Infer the type of an already-elaborated term that may still
        contain metavariables.  For simple atoms we compute directly;
        for compound terms (Lam, Pi, Let, App) we recursively elaborate
        children (which may themselves invoke metas) and then assemble."""
        if isinstance(e, Sort):
            return Sort(LSucc(e.level))
        if isinstance(e, Const):
            decl = self.env.get(e.name)
            ty = getattr(decl, "type_", None)
            if ty is None:
                raise ElabError(f"declaration {e.name} has no type")
            return inst_levels(ty, getattr(decl, "level_params", ()), e.levels)
        if isinstance(e, BVar):
            raise ElabError(f"unbound BVar in elaborated term")
        if isinstance(e, FVar):
            ty, _ = ctx.lookup(e.name)
            return ty
        if isinstance(e, Meta):
            return self.mctx.get_type(e.id)
        if isinstance(e, App):
            # rare: only happens when _spine left us with an App head;
            # fall back to kernel for safety
            ty, _ = self.kernel.infer(self.mctx.instantiate(e), ctx)
            return ty
        if isinstance(e, Lam):
            dom_resolved = _resolve_bvars(e.dom, ctx)
            fv = ctx.push(e.binder, dom_resolved)
            try:
                body_ty = self._infer_elaborated(
                    open_(e.body, FVar(fv, dom_resolved)), ctx)
                return Pi(e.binder, dom_resolved, close(body_ty, fv), False)
            finally:
                ctx.pop()
        if isinstance(e, Pi):
            # Sort (imax dom-level body-level); we approximate by Sort 0
            # — this branch is rarely needed mid-elaboration.  Kernel
            # gives the real answer post-instantiation.
            ty, _ = self.kernel.infer(self.mctx.instantiate(e), ctx)
            return ty
        if isinstance(e, Let):
            ty, _ = self.kernel.infer(self.mctx.instantiate(e), ctx)
            return ty
        raise TypeError(e)


    def _elab_lam_with_expected(self, lam: Lam, expected: Expr,
                                  ctx: LocalCtx) -> Tuple[Expr, Expr]:
        """Elaborate a Lam against an expected Pi type, propagating the
        expected body to inner elaboration (so `by` etc. see it)."""
        exp_w = self.kernel.whnf(self.mctx.instantiate(expected), ctx)
        if not isinstance(exp_w, Pi):
            # fall back: just elab the Lam as an atom
            head_e = self._elab_atom(lam, ctx)
            head_ty = self._infer_elaborated(head_e, ctx)
            return head_e, head_ty
        dom_resolved = _resolve_bvars(lam.dom, ctx)
        fv = ctx.push(lam.binder, dom_resolved)
        try:
            body_open = open_(lam.body, FVar(fv, dom_resolved))
            body_expected = open_(exp_w.body, FVar(fv, dom_resolved))
            body_e, body_ty = self.elab(body_open, body_expected, ctx)
            body_e = self.mctx.instantiate(body_e)
            body_ty = self.mctx.instantiate(body_ty)
            elab_lam = Lam(lam.binder, dom_resolved, close(body_e, fv))
            elab_ty = Pi(lam.binder, dom_resolved, close(body_ty, fv), False)
            return elab_lam, elab_ty
        finally:
            ctx.pop()

    # -- tactic interpreter --
    #
    # Each tactic returns `(term, subgoal_meta_ids)`.  Tactics that solve
    # the goal completely return an empty subgoal list.  `apply` may
    # return non-empty subgoals — meta IDs that subsequent tactics in the
    # `;`-sequence must fill in order.  `seq` drains the subgoal queue
    # using the rest of the tactics.

    def _run_tactic_by(self, by_node: By, goal: Expr, ctx: LocalCtx) -> Expr:
        """Top-level entry point for `by TAC`.  Runs the tactic against
        `goal` in the elaborator's current context, returns the term."""
        from .lean_parser import get_tactic
        tac = get_tactic(by_node.tac_id)
        term, subs = self._run_tactic(tac, goal, ctx)
        # Any leftover subgoals at the top level are an error — they
        # should have been drained by `seq`.  (A leftover that's been
        # auto-pinned by unification is fine.)
        unresolved = [m for m in subs if self.mctx.get(m) is None]
        if unresolved:
            tys = "; ".join(
                show_expr(self.mctx.instantiate(self.mctx.get_type(m)))
                for m in unresolved)
            raise ElabError(f"unsolved subgoals after tactic block: {tys}")
        return self.mctx.instantiate(term)

    def _run_tactic(self, tac: tuple, goal: Expr,
                    ctx: LocalCtx) -> Tuple[Expr, List[int]]:
        kind = tac[0]
        if kind == "rfl":
            # Goal must be `Eq.{u} α a b` with a ≡ b (defeq).
            goal_w = self.kernel.whnf(self.mctx.instantiate(goal), ctx)
            head, args = _spine(goal_w)
            if not (isinstance(head, Const) and head.name == "Eq"
                    and len(args) == 3):
                raise ElabError(
                    f"rfl: goal is not `Eq _ _ _`, got {show_expr(goal_w)}")
            α, a, b = args
            if not self.kernel.def_eq(a, b, ctx):
                raise ElabError(
                    f"rfl: sides differ:\n"
                    f"  lhs = {show_expr(self.mctx.instantiate(a))}\n"
                    f"  rhs = {show_expr(self.mctx.instantiate(b))}")
            lvls = head.levels
            return App(App(Const("Eq.refl", lvls), α), a), []

        if kind == "exact":
            _, expr, _bvar_stack = tac
            # The stored expr has BVars from the tactic-parse scope.
            # Resolve them against the elaborator's current ctx (which
            # has FVars for each prior `intro`).
            expr_r = _resolve_bvars(expr, ctx)
            e_elab, _ = self.elab(expr_r, goal, ctx)
            return e_elab, []

        if kind == "assumption":
            # Walk local FVars innermost-first; succeed on the first
            # whose type is def-equal to the goal.
            goal_inst = self.mctx.instantiate(goal)
            for name, fv_ty, _val in reversed(ctx.entries):
                if self.kernel.def_eq(fv_ty, goal_inst, ctx):
                    return FVar(name, fv_ty), []
            raise ElabError(
                f"assumption: no hypothesis matches goal "
                f"{show_expr(goal_inst)}")

        if kind == "apply":
            _, expr, _bvar_stack = tac
            expr_r = _resolve_bvars(expr, ctx)
            # Elaborate without an expected type — we want the full
            # function type so we can peel it ourselves.
            e_elab, e_ty = self.elab(expr_r, None, ctx)
            # Peel every leading Π, generating a fresh meta for each
            # binder.  Track explicit metas as candidate subgoals;
            # inst-implicit metas get synthesised after unification.
            explicit_metas: List[int] = []
            inst_metas: List[Tuple[Meta, Expr]] = []
            cur_ty = self.mctx.instantiate(e_ty)
            cur_ty_w = self.kernel.whnf(cur_ty, ctx)
            cur_ty_w = self.mctx.instantiate(cur_ty_w)
            while isinstance(cur_ty_w, Pi):
                m = self.mctx.fresh(cur_ty_w.dom)
                e_elab = App(e_elab, m)
                if cur_ty_w.inst_implicit:
                    inst_metas.append((m, cur_ty_w.dom))
                elif not cur_ty_w.implicit:
                    explicit_metas.append(m.id)
                cur_ty = subst_bvar(cur_ty_w.body, 0, m)
                cur_ty = self.mctx.instantiate(cur_ty)
                cur_ty_w = self.kernel.whnf(cur_ty, ctx)
                cur_ty_w = self.mctx.instantiate(cur_ty_w)
            # Unify the function's return type with the goal.  This is
            # what pins the implicit/inst metas (and potentially some
            # explicit ones too).
            if not unify(cur_ty, goal, ctx, self.mctx, self.kernel,
                         type_of=lambda x: self._infer_elaborated(x, ctx)):
                if not self.kernel.def_eq(cur_ty, goal, ctx):
                    raise ElabError(
                        f"apply: function's return type doesn't match goal:\n"
                        f"  goal     {show_expr(self.mctx.instantiate(goal))}\n"
                        f"  function {show_expr(self.mctx.instantiate(cur_ty))}")
            # Synthesise inst-implicit metas (now their types are pinned).
            for m, dom in inst_metas:
                if self.mctx.get(m.id) is not None:
                    continue
                sub = self._synthesize(self.mctx.instantiate(dom), ctx)
                if sub is None:
                    raise ElabError(
                        f"apply: failed to synthesize instance for "
                        f"{show_expr(self.mctx.instantiate(dom))}")
                self.mctx.assign(m.id, sub)
            # Only return explicit metas that unification didn't auto-solve.
            remaining = [m for m in explicit_metas if self.mctx.get(m) is None]
            return e_elab, remaining

        if kind == "intro":
            # Standalone intro outside a seq has no body to wrap.
            raise ElabError(
                "intro must appear inside a `;`-sequence with at least "
                "one body tactic after it (e.g. `intro x; exact x`)")

        if kind == "seq":
            _, tacs = tac
            return self._run_seq(tacs, goal, ctx)

        raise ElabError(f"unknown tactic kind: {kind}")

    def _run_seq(self, tacs: list, goal: Expr,
                 ctx: LocalCtx) -> Tuple[Expr, List[int]]:
        """Run a tactic sequence.

        Leading `intro`s peel Π binders off the goal, pushing fresh FVars
        onto `ctx`.  The first non-intro tactic produces the main term;
        any subgoals it leaves are drained by the trailing tactics in
        order.  After everything resolves, we wrap a Lam for each
        introduced binder (innermost first), closing over its FVar.

        Subsequent tactics that solve subgoals see the EXTENDED ctx — so
        e.g. `intro h; apply f h; rfl` works even when the rfl is the
        last tactic and `apply` produced a subgoal that doesn't reference
        `h`.  This is the structural alternative to abstracting escaped
        subgoals over the introduced binder."""
        if not tacs:
            raise ElabError("empty tactic sequence")
        # Phase 1: consume leading intros.
        intro_stack: List[Tuple[str, Expr, str]] = []     # (name, dom, fv)
        cur_goal = goal
        i = 0
        try:
            while i < len(tacs) and tacs[i][0] == "intro":
                name = tacs[i][1]
                goal_w = self.kernel.whnf(
                    self.mctx.instantiate(cur_goal), ctx)
                if not isinstance(goal_w, Pi):
                    raise ElabError(
                        f"intro {name!r}: goal is not a Π, got "
                        f"{show_expr(goal_w)}")
                dom = goal_w.dom
                fv = ctx.push(name, dom)
                intro_stack.append((name, dom, fv))
                cur_goal = open_(goal_w.body, FVar(fv, dom))
                i += 1
            if i == len(tacs):
                raise ElabError(
                    "tactic sequence ends with intro — needs a body tactic")
            # Phase 2: main tactic + drain its subgoals with trailing tacs.
            main_tac = tacs[i]
            rest = tacs[i + 1:]
            main_term, sub_metas = self._run_tactic(main_tac, cur_goal, ctx)
            queue = list(sub_metas)
            rest_iter = iter(rest)
            while True:
                while queue and self.mctx.get(queue[0]) is not None:
                    queue.pop(0)
                if not queue:
                    break
                meta_id = queue.pop(0)
                try:
                    sub_tac = next(rest_iter)
                except StopIteration:
                    meta_ty = self.mctx.instantiate(
                        self.mctx.get_type(meta_id))
                    raise ElabError(
                        f"unsolved subgoal: ?m{meta_id} : "
                        f"{show_expr(meta_ty)}")
                meta_ty = self.mctx.instantiate(self.mctx.get_type(meta_id))
                sub_term, sub_metas_new = self._run_tactic(
                    sub_tac, meta_ty, ctx)
                sub_term = self.mctx.instantiate(sub_term)
                self.mctx.assign(meta_id, sub_term)
                queue.extend(sub_metas_new)
            extra = list(rest_iter)
            if extra:
                raise ElabError(
                    f"extra tactics after all goals solved "
                    f"({len(extra)} unused)")
            main_term = self.mctx.instantiate(main_term)
            # Phase 3: wrap Lams (innermost-first).
            for name, dom, fv in reversed(intro_stack):
                main_term = Lam(name, dom, close(main_term, fv))
            return main_term, []
        finally:
            for _ in intro_stack:
                ctx.pop()

    # -- instance synthesis --

    def _save_mctx(self):
        return (
            {i: info.assignment for i, info in self.mctx.metas.items()},
            dict(self.mctx.level_metas),
            self.mctx._next_id,
            self.mctx._next_lid,
        )

    def _restore_mctx(self, saved):
        assigns, level_assigns, next_id, next_lid = saved
        for i in list(self.mctx.metas.keys()):
            if i >= next_id:
                del self.mctx.metas[i]
            else:
                self.mctx.metas[i].assignment = assigns[i]
        for i in list(self.mctx.level_metas.keys()):
            if i >= next_lid:
                del self.mctx.level_metas[i]
            else:
                self.mctx.level_metas[i] = level_assigns[i]
        self.mctx._next_id = next_id
        self.mctx._next_lid = next_lid

    def _synthesize(self, goal: Expr, ctx: LocalCtx) -> Optional[Expr]:
        """Find a term of type `goal`:
          (1) local-context lookup,
          (2) backtracking search through registered instances,
              including parametric instances whose dependencies are
              themselves synthesised recursively (after unifying with
              the goal so dependency types are pinned down).
        """
        goal_w = self.kernel.whnf(self.mctx.instantiate(goal), ctx)
        head, _args = _spine(goal_w)
        if not isinstance(head, Const):
            return None
        class_head = head.name

        # (1) Local context
        for fv_name, fv_ty, _val in ctx.entries:
            fv_ty_w = self.kernel.whnf(fv_ty, ctx)
            fv_head, _ = _spine(fv_ty_w)
            if isinstance(fv_head, Const) and fv_head.name == class_head:
                saved = self._save_mctx()
                if unify(fv_ty, goal, ctx, self.mctx, self.kernel,
                         type_of=lambda x: self._infer_elaborated(x, ctx)):
                    return FVar(fv_name, fv_ty)
                self._restore_mctx(saved)

        # (2) Registered instances, with backtracking
        for inst_name in self.env.instances_of(class_head):
            saved = self._save_mctx()
            try:
                result = self._try_instance(inst_name, goal, ctx)
            except Exception:
                result = None
            if result is not None:
                return result
            self._restore_mctx(saved)
        return None

    def _try_instance(self, inst_name: str, goal: Expr,
                       ctx: LocalCtx) -> Optional[Expr]:
        """Attempt to use `inst_name` to construct a value of type `goal`.

        Two-pass strategy:
          1. Allocate metas for all the instance's implicit / inst-
             implicit binders.  Don't try to synthesise yet — that
             would mostly fail because the binder types still have
             unfilled metas.
          2. Unify the instance's head type with `goal`.  This pins
             down the per-class-argument metas.
          3. NOW walk the inst-implicit metas and synthesise them
             (their types are concrete enough at this point).
        """
        decl = self.env.get(inst_name)
        lps = getattr(decl, "level_params", ())
        inst_lvls = tuple(self.mctx.fresh_level() for _ in lps)
        inst_ty = inst_levels(getattr(decl, "type_"), lps, inst_lvls)

        # Allocate placeholders.  For each binder, remember its kind
        # (implicit vs inst-implicit) and the metavariable.
        applied_args: List[Tuple[Meta, str, Expr]] = []
        cur = self.kernel.whnf(inst_ty, ctx)
        while isinstance(cur, Pi) and (cur.implicit or cur.inst_implicit):
            m = self.mctx.fresh(cur.dom)
            kind = "inst" if cur.inst_implicit else "impl"
            applied_args.append((m, kind, cur.dom))
            cur = self.kernel.whnf(self.mctx.instantiate(subst_bvar(cur.body, 0, m)),
                                    ctx)
        # `cur` is now the instance head, fully applied to metas.
        if not unify(cur, goal, ctx, self.mctx, self.kernel,
                     type_of=lambda x: self._infer_elaborated(x, ctx)):
            return None
        # Solve the inst-implicit metas (their types' metas are now bound)
        for m, kind, dom in applied_args:
            if kind == "inst":
                sub_goal = self.mctx.instantiate(dom)
                sub = self._synthesize(sub_goal, ctx)
                if sub is None:
                    return None
                self.mctx.assign(m.id, sub)
        # Build the application
        result: Expr = Const(inst_name, inst_lvls)
        for m, _, _ in applied_args:
            result = App(result, m)
        return result


def _remap_for_proj(e: Expr, field_idx: int, n_params: int) -> Expr:
    """Remap a field-type's BVars from the field-parse scope to a
    projection-body scope.

    Field-i parse scope:  innermost-first  =  [field_{i-1}, ..., field_0, param_{n-1}, ..., param_0]
    Projection body scope (inside Π self): innermost-first = [self, param_{n-1}, ..., param_0]

    Non-dependent record assumption: e doesn't reference any previous
    field (so any BVar(k) with k < field_idx is a bug).  Param BVars
    at parse-scope positions [field_idx, field_idx + n_params) map to
    projection-scope positions [1, 1 + n_params)."""
    def walk(t: Expr, cutoff: int) -> Expr:
        if isinstance(t, BVar):
            if t.idx < cutoff:
                return t                                 # local binder
            local = t.idx - cutoff
            if local < field_idx:
                raise NotImplementedError(
                    "dependent record fields are not supported")
            new_local = local - field_idx + 1            # shift past prev fields, add self
            return BVar(cutoff + new_local)
        if isinstance(t, (Sort, FVar, Const, Meta)):
            return t
        if isinstance(t, Explicit):
            return Explicit(walk(t.inner, cutoff))
        if isinstance(t, App):
            return App(walk(t.fn, cutoff), walk(t.arg, cutoff))
        if isinstance(t, Lam):
            return Lam(t.binder, walk(t.dom, cutoff), walk(t.body, cutoff + 1))
        if isinstance(t, Pi):
            return Pi(t.binder, walk(t.dom, cutoff), walk(t.body, cutoff + 1),
                      t.implicit, t.inst_implicit)
        if isinstance(t, Let):
            return Let(t.binder, walk(t.type_, cutoff),
                       walk(t.value, cutoff), walk(t.body, cutoff + 1))
        return t
    return walk(e, 0)


def _resolve_bvars(e: Expr, ctx: LocalCtx, cutoff: int = 0) -> Expr:
    """Replace free BVars (those referring to ctx entries) with the
    corresponding FVars.  Bound BVars (those introduced by binders
    inside `e`) are preserved using a depth cutoff."""
    if isinstance(e, BVar):
        if e.idx < cutoff:
            return e
        ridx = e.idx - cutoff
        if ridx < len(ctx.entries):
            entry = ctx.entries[-(ridx + 1)]
            return FVar(entry[0], entry[1])
        return e
    if isinstance(e, (Sort, FVar, Const, Meta)):
        return e
    if isinstance(e, Explicit):
        return Explicit(_resolve_bvars(e.inner, ctx, cutoff))
    if isinstance(e, App):
        return App(_resolve_bvars(e.fn, ctx, cutoff),
                   _resolve_bvars(e.arg, ctx, cutoff))
    if isinstance(e, Lam):
        return Lam(e.binder, _resolve_bvars(e.dom, ctx, cutoff),
                   _resolve_bvars(e.body, ctx, cutoff + 1))
    if isinstance(e, Pi):
        return Pi(e.binder, _resolve_bvars(e.dom, ctx, cutoff),
                  _resolve_bvars(e.body, ctx, cutoff + 1),
                  e.implicit, e.inst_implicit)
    if isinstance(e, Let):
        return Let(e.binder, _resolve_bvars(e.type_, ctx, cutoff),
                   _resolve_bvars(e.value, ctx, cutoff),
                   _resolve_bvars(e.body, ctx, cutoff + 1))
    return e


def _spine(e: Expr):
    """Return (head, [arg1, arg2, ...]) from a left-associated App chain."""
    args = []
    while isinstance(e, App):
        args.insert(0, e.arg)
        e = e.fn
    return e, args


# ---------------- driver ----------------

def elaborate_decl(env: Env, kind: str, name: str = None,
                   level_params: Tuple[str, ...] = (),
                   ty: Expr = None, body: Optional[Expr] = None,
                   **extra) -> None:
    """Elaborate a declaration and add it to env (kernel-checked).

    `kind` may be 'def', 'theorem', 'axiom', 'instance', 'inductive',
    or 'structure'.
    """
    if kind == "inductive":
        _process_inductive(env, name, level_params, extra["params"],
                           extra["result_ty"], extra["ctors"])
        return
    if kind == "structure":
        _process_structure(env, name, level_params, extra["params"],
                           extra["result_ty"], extra["fields"],
                           is_class=extra.get("is_class", False))
        return
    ker = Kernel(env)
    # Elaborate the TYPE first — types may contain `f x` where `f` has
    # implicit binders that need filling in (otherwise the kernel sees
    # the wrong β-reduction).
    ty_elab_ctx = Elaborator(env)
    ty_elab, _ = ty_elab_ctx.elab(ty, None, LocalCtx())
    ty_elab = ty_elab_ctx.mctx.instantiate_fully(ty_elab)
    if kind == "axiom":
        ker.add_axiom(Axiom(name=name, level_params=level_params, type_=ty_elab))
        return
    assert body is not None
    elab = Elaborator(env)
    body_e, body_ty = elab.elab(body, ty_elab, LocalCtx())
    body_e = elab.mctx.instantiate_fully(body_e)
    ker.add_definition(Definition(
        name=name, level_params=level_params,
        type_=ty_elab, value=body_e))
    if kind == "instance":
        t = ty_elab
        while isinstance(t, Pi):
            t = t.body
        head, _ = _spine(t)
        if isinstance(head, Const):
            env.register_instance(name, head.name)


def _process_inductive(env, name, lvl_params, params, result_ty, ctors):
    """Convert parsed inductive into InductiveSpec and compile it."""
    from .inductive import (
        InductiveSpec, CtorSpec, inductive_self, compile_inductive,
    )
    # Detect self-applications in field types.
    def _maybe_self(field_ty):
        head, _args = _spine(field_ty)
        if isinstance(head, Const) and head.name == name:
            return inductive_self()
        return field_ty

    ctor_specs = []
    for ctor_name, fields, _ctor_ret in ctors:
        # If the user wrote a bare ctor name (e.g. `| nil`), prefix it
        # with the inductive's name (`MyBool.nil`).  If they wrote a
        # qualified name already (`MyBool.nil`), leave it.
        full = ctor_name if "." in ctor_name else f"{name}.{ctor_name}"
        arg_types = tuple((fname, _maybe_self(fty))
                          for fname, fty, _impl, _inst in fields)
        ctor_specs.append(CtorSpec(name=full, arg_types=arg_types))

    spec = InductiveSpec(
        name=name,
        level_params=lvl_params,
        params=tuple((p[0], p[1]) for p in params),
        sort=result_ty,
        constructors=tuple(ctor_specs),
    )
    compile_inductive(env, spec)


def _process_structure(env, name, lvl_params, params, result_ty, fields,
                       is_class=False):
    """Desugar `structure`/`class` to a single-ctor `inductive`, then
    generate non-dependent projections via the recursor.

    For `class` declarations the generated projection makes the
    structure's parameters implicit and the `self` argument
    inst-implicit, so the user can write `Add.add x y` and have the
    elaborator infer the type argument and synthesize the instance."""
    from .inductive import (
        InductiveSpec, CtorSpec, inductive_self, compile_inductive,
    )
    ctor_name = f"{name}.mk"
    arg_types = tuple((fname, fty)
                      for fname, fty, _impl, _inst in fields)
    spec = InductiveSpec(
        name=name,
        level_params=lvl_params,
        params=tuple((p[0], p[1]) for p in params),
        sort=result_ty,
        constructors=(CtorSpec(name=ctor_name, arg_types=arg_types),),
    )
    compile_inductive(env, spec)
    _generate_projections(env, name, lvl_params, params, fields,
                          is_class=is_class)


def _generate_projections(env, ind_name, lvl_params, params, fields,
                           is_class=False):
    """Auto-generate projection definitions for a structure / class."""
    from .levels import LSucc, LZero, LParam, LMax
    from .env import Definition

    n_params = len(params)
    n_fields = len(fields)
    # Build  ind_applied = Const(ind_name, lvls) p_0 .. p_{n_params-1}
    # as it appears INSIDE the projection's binders.
    def ind_at(depth):
        head_e: Expr = Const(ind_name, tuple(LParam(l) for l in lvl_params))
        # params at the projection's call site sit at BVar(depth + n_params - 1 - i)
        for i in range(n_params):
            head_e = App(head_e, BVar(depth + (n_params - 1 - i)))
        return head_e

    rec_name = f"{ind_name}.rec"
    rec_decl = env.get(rec_name)
    motive_lvl_param = rec_decl.motive_universe_param
    for i, (fname, fty, _impl, _inst) in enumerate(fields):
        proj_name = f"{ind_name}.{fname}"
        if env.has(proj_name):
            continue
        # Field i was parsed in scope: [params, field_0, ..., field_{i-1}].
        # The projection's body sits in scope: [params, self].
        # Non-dependent record assumption: fty doesn't reference any
        # previous field (BVars < i are forbidden).  Then param BVars
        # at positions [i, i+n_params) need to be remapped to [1, 1+n_params).
        # That's `shift by (1 - i)` for BVars >= i, or equivalently
        # n_params subst_bvar peels to drop previous-field slots followed
        # by a shift to insert the `self` binder.
        from .expr import shift as _se
        ty_inside_self = _remap_for_proj(fty, i, n_params)
        # For classes, mark `self` as inst-implicit and parameters as
        # implicit so projections can be called without manually
        # supplying them.  Plain structures keep them explicit.
        proj_ty = Pi("self", ind_at(0), ty_inside_self,
                     False, is_class)
        for p in reversed(params):
            pname, pty = p[0], p[1]
            proj_ty = Pi(pname, pty, proj_ty, is_class, False)
        # projection body: λ params, λ self,
        #   Name.rec.{lvls, motive_lvl}
        #     params...  (motive := λ _ : Name params, T_i)
        #     (λ f_0 ... f_{n-1}, f_i)  self
        # Motive sits at projection-body scope (inside λ-params + λ-self).
        # Motive domain `Name params` references α at BVar(1) for one param.
        # Motive body T_i sits inside the motive's own `_` binder.
        # Remap T_i from field-parse scope to projection scope (shift by
        # `1 - i`), then shift by 1 more for the motive's own binder.
        motive_dom = ind_at(1)
        motive = Lam("_", motive_dom, _se(_remap_for_proj(fty, i, n_params), 1))
        # Build minor: λ f_0 : F_0. λ f_1 : F_1. ... λ f_{n-1} : F_{n-1}. f_i
        # Inside the minor, BVar(0) = f_{n-1}, BVar(1) = f_{n-2}, ..., BVar(n-1-i) = f_i.
        minor_body: Expr = BVar(n_fields - 1 - i)
        # wrap from innermost out: f_{n-1}, ..., f_0
        for j in reversed(range(n_fields)):
            f_name, f_ty, _, _ = fields[j]
            # f_ty was parsed in scope = (params, field_0, ..., field_{j-1}).
            # In the minor's binder-j type position, the surrounding scope is
            # (field_{j-1}, ..., field_0, self, params...).  We want:
            #   * fty's references to previous fields (BVar indices 0..j-1)
            #     to stay put,
            #   * fty's references to params (BVar indices >= j) to shift up
            #     by 1 (to account for the new `self` binder we inserted).
            # That's shift(f_ty, d=1, cutoff=j).
            minor_body = Lam(f_name, _se(f_ty, 1, j), minor_body)
        # Apply rec: head is Name.rec.{params_lvls + motive_lvl}.
        # Leave the motive level empty so the elaborator instantiates it
        # with a fresh level meta and solves it from context.
        rec_e: Expr = Const(rec_name, ())
        # apply params
        for k in range(n_params):
            # param k at this point is at BVar(n_params - 1 - k + 1) inside Πself
            rec_e = App(rec_e, BVar(n_params - 1 - k + 1))
        rec_e = App(rec_e, motive)
        rec_e = App(rec_e, minor_body)
        # major = self (BVar 0 at this scope)
        rec_e = App(rec_e, BVar(0))

        # wrap the body with Π-self λ, then param λs
        proj_value: Expr = rec_e
        proj_value = Lam("self", ind_at(0), proj_value)
        for p in reversed(params):
            proj_value = Lam(p[0], p[1], proj_value)

        # Elaborate (so the motive's level meta gets solved) then add.
        elab = Elaborator(env)
        body_e, _body_ty = elab.elab(proj_value, proj_ty, LocalCtx())
        body_e = elab.mctx.instantiate_fully(body_e)
        from .kernel import Kernel
        ker = Kernel(env)
        ker.add_definition(Definition(
            name=proj_name,
            level_params=lvl_params,
            type_=proj_ty,
            value=body_e,
        ))
