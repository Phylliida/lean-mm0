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
    shift, subst_bvar, open_, close, inst_levels, beta, show as show_expr,
)
from .env import Env, Definition, Theorem, Axiom, Constructor, Recursor, Inductive
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


def _references_fvar(e: Expr, name: str) -> bool:
    """Returns True if `e` contains an FVar named `name`.  Used by
    `revert` to refuse popping a hypothesis that a later one depends on."""
    if isinstance(e, FVar):
        return e.name == name
    if isinstance(e, (Sort, BVar, Const, Meta, By)):
        return False
    if isinstance(e, Explicit):
        return _references_fvar(e.inner, name)
    if isinstance(e, App):
        return _references_fvar(e.fn, name) or _references_fvar(e.arg, name)
    if isinstance(e, (Lam, Pi)):
        return _references_fvar(e.dom, name) or _references_fvar(e.body, name)
    if isinstance(e, Let):
        return (_references_fvar(e.type_, name)
                or _references_fvar(e.value, name)
                or _references_fvar(e.body, name))
    return False


def _beta_norm(e: Expr) -> Expr:
    """Beta-only normalisation: reduce every `(λx. body) arg` redex
    recursively, without doing δ (definition unfolding) or ι (recursor
    reduction).  Used to expose the real shape of a goal that came out of
    a recursor minor — those goals look like `(λk. motive k) (ctor args)`
    and the `rewrite` tactic's structural search can't see through the
    application until it's been β-reduced."""
    if isinstance(e, (Sort, BVar, FVar, Const, Meta, By)):
        return e
    if isinstance(e, Explicit):
        return Explicit(_beta_norm(e.inner))
    if isinstance(e, App):
        fn = _beta_norm(e.fn)
        arg = _beta_norm(e.arg)
        if isinstance(fn, Lam):
            return _beta_norm(beta(fn.body, arg))
        return App(fn, arg)
    if isinstance(e, Lam):
        return Lam(e.binder, _beta_norm(e.dom), _beta_norm(e.body))
    if isinstance(e, Pi):
        return Pi(e.binder, _beta_norm(e.dom), _beta_norm(e.body),
                  e.implicit, e.inst_implicit)
    if isinstance(e, Let):
        return Let(e.binder, _beta_norm(e.type_),
                   _beta_norm(e.value), _beta_norm(e.body))
    return e


def _replace_term(e: Expr, target: Expr, replacement: Expr) -> Tuple[Expr, bool]:
    """Walk `e` substituting `replacement` for every subterm structurally
    equal to `target`.  Returns (new_expr, found_any).  When descending
    into a Lam/Pi/Let body, shifts both `target` and `replacement` by 1
    so BVar references stay consistent."""
    if e == target:
        return replacement, True
    if isinstance(e, (Sort, BVar, FVar, Const, Meta, By)):
        return e, False
    if isinstance(e, Explicit):
        inner_new, f = _replace_term(e.inner, target, replacement)
        return Explicit(inner_new), f
    if isinstance(e, App):
        fn_new, f1 = _replace_term(e.fn, target, replacement)
        arg_new, f2 = _replace_term(e.arg, target, replacement)
        return App(fn_new, arg_new), f1 or f2
    if isinstance(e, Lam):
        dom_new, f1 = _replace_term(e.dom, target, replacement)
        body_new, f2 = _replace_term(
            e.body, shift(target, 1), shift(replacement, 1))
        return Lam(e.binder, dom_new, body_new), f1 or f2
    if isinstance(e, Pi):
        dom_new, f1 = _replace_term(e.dom, target, replacement)
        body_new, f2 = _replace_term(
            e.body, shift(target, 1), shift(replacement, 1))
        return Pi(e.binder, dom_new, body_new,
                  e.implicit, e.inst_implicit), f1 or f2
    if isinstance(e, Let):
        type_new, f1 = _replace_term(e.type_, target, replacement)
        value_new, f2 = _replace_term(e.value, target, replacement)
        body_new, f3 = _replace_term(
            e.body, shift(target, 1), shift(replacement, 1))
        return Let(e.binder, type_new, value_new, body_new), f1 or f2 or f3
    raise TypeError(e)


def _subgoal_meta_id(sub) -> int:
    """A subgoal is either a bare meta_id (legacy) or (meta_id, ctx_snap)."""
    return sub[0] if isinstance(sub, tuple) else sub


def _subgoal_unpack(sub, ctx):
    """Unpack (meta_id, ctx_snap).  For a legacy bare meta_id, fall back
    to the current ctx as the snapshot."""
    if isinstance(sub, tuple):
        return sub[0], sub[1]
    return sub, tuple(ctx.entries)


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
    # Each tactic returns `(term, subgoals)`.  A subgoal is either a bare
    # meta_id (legacy) or a tuple `(meta_id, ctx_snap)` — the ctx_snap is
    # a snapshot of `ctx.entries` from where the subgoal was created.
    # `seq` uses these snapshots to run later tactics in the right ctx
    # (so e.g. `apply f` made inside `intro h` produces subgoals whose
    # solving tactics still see `h`).

    def _run_tactic_by(self, by_node: By, goal: Expr, ctx: LocalCtx) -> Expr:
        """Top-level entry point for `by TAC`.  Runs the tactic against
        `goal` in the elaborator's current context, returns the term."""
        from .lean_parser import get_tactic
        tac = get_tactic(by_node.tac_id)
        term, subs = self._run_tactic(tac, goal, ctx)
        # Any leftover subgoals at the top level are an error — they
        # should have been drained by `seq`.  (A leftover that's been
        # auto-pinned by unification is fine.)
        unresolved = [s for s in subs
                      if self.mctx.get(_subgoal_meta_id(s)) is None]
        if unresolved:
            tys = "; ".join(
                show_expr(self.mctx.instantiate(
                    self.mctx.get_type(_subgoal_meta_id(s))))
                for s in unresolved)
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
            # Snapshot ctx so the subgoals can later be solved by tactics
            # that may run in a different ctx (e.g. after the seq has
            # popped some intros).
            ctx_snap = tuple(ctx.entries)
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
            remaining = [(m, ctx_snap) for m in explicit_metas
                         if self.mctx.get(m) is None]
            return e_elab, remaining

        if kind == "cases":
            _, expr, _bvar_stack = tac
            expr_r = _resolve_bvars(expr, ctx)
            scrut_e, scrut_ty = self.elab(expr_r, None, ctx)
            scrut_ty_w = self.kernel.whnf(
                self.mctx.instantiate(scrut_ty), ctx)
            head, ind_args = _spine(scrut_ty_w)
            if not isinstance(head, Const) or not self.env.has(head.name):
                raise ElabError(
                    f"cases: scrutinee type is not an inductive: "
                    f"{show_expr(scrut_ty_w)}")
            decl = self.env.get(head.name)
            if not isinstance(decl, Inductive):
                raise ElabError(
                    f"cases: {head.name} is not an inductive")
            rec_decl = self.env.get(decl.recursor_name)
            n_params = decl.num_params
            n_indices = decl.num_indices
            param_args = ind_args[:n_params]
            index_args = ind_args[n_params:n_params + n_indices]
            ind_lvls = head.levels
            G = self.mctx.instantiate(goal)
            # Build the motive: λ idx_0 … idx_{i-1}. λ scrut. G_shifted.
            # Non-dependent motive (body ignores the new binders), so we
            # just shift G past n_indices + 1 binders.
            # `ind_applied` is the scrut binder's domain — it lives one
            # level under the index binders, so its param args shift by
            # n_indices and the index slots use BVars (innermost-last).
            ind_applied = Const(decl.name, ind_lvls)
            for pa in param_args:
                ind_applied = App(ind_applied, shift(pa, n_indices))
            for i in range(n_indices):
                ind_applied = App(ind_applied, BVar(n_indices - 1 - i))
            motive = Lam("_scrut", ind_applied, shift(G, n_indices + 1))
            if n_indices > 0:
                # Wrap with index binders; the index types come from the
                # inductive's signature (Π params, Π indices, Sort _).
                ind_ty = inst_levels(decl.type_, decl.level_params, ind_lvls)
                for pa in param_args:
                    if not isinstance(ind_ty, Pi):
                        raise ElabError(
                            f"cases: {decl.name} has bad inductive type")
                    ind_ty = subst_bvar(ind_ty.body, 0, pa)
                index_types: list = []
                cur_ty = ind_ty
                for _ in range(n_indices):
                    if not isinstance(cur_ty, Pi):
                        raise ElabError(
                            f"cases: {decl.name} has bad inductive type")
                    index_types.append(cur_ty.dom)
                    cur_ty = cur_ty.body
                for i in reversed(range(n_indices)):
                    motive = Lam(f"_i{i}", index_types[i], motive)
            G_ty_w = self.kernel.whnf(
                self.mctx.instantiate(self._infer_elaborated(G, ctx)),
                ctx)
            if not isinstance(G_ty_w, Sort):
                raise ElabError(
                    f"cases: goal's type isn't a Sort: "
                    f"{show_expr(G_ty_w)}")
            v_level = G_ty_w.level
            ctx_snap = tuple(ctx.entries)
            minors = []
            subgoals_out: list = []
            for ctor_name in decl.constructor_names:
                cd = self.env.get(ctor_name)
                ct = inst_levels(cd.type_, cd.level_params, ind_lvls)
                for pa in param_args:
                    if not isinstance(ct, Pi):
                        raise ElabError(
                            f"cases: bad ctor type for {ctor_name}")
                    ct = subst_bvar(ct.body, 0, pa)
                field_types = []
                for _ in range(cd.num_fields):
                    if not isinstance(ct, Pi):
                        raise ElabError(
                            f"cases: bad ctor type for {ctor_name}")
                    field_types.append(ct.dom)
                    ct = ct.body
                rec_rule = next(
                    (r for r in rec_decl.rules
                     if r.ctor_name == ctor_name), None)
                rec_positions = (rec_rule.rec_arg_positions
                                 if rec_rule else ())
                n_fields = cd.num_fields
                n_rec = len(rec_positions)
                # Minor type: Π fields, Π IHs, G (shifted by n_fields+n_rec).
                # For non-dependent motive every IH type is just G shifted
                # to the right depth (motive is constant).
                minor_ty = shift(G, n_fields + n_rec)
                for k in reversed(range(n_rec)):
                    minor_ty = Pi(f"ih{k}",
                                   shift(G, n_fields + k),
                                   minor_ty)
                for j in reversed(range(n_fields)):
                    minor_ty = Pi(f"f{j}", field_types[j], minor_ty)
                m = self.mctx.fresh(minor_ty)
                minors.append(m)
                subgoals_out.append((m.id, ctx_snap))
            rec_lvls: list = []
            for lp_name in rec_decl.level_params:
                if lp_name == rec_decl.motive_universe_param:
                    rec_lvls.append(v_level)
                else:
                    idx = decl.level_params.index(lp_name)
                    rec_lvls.append(ind_lvls[idx])
            rec_term: Expr = Const(rec_decl.name, tuple(rec_lvls))
            for pa in param_args:
                rec_term = App(rec_term, pa)
            rec_term = App(rec_term, motive)
            for m in minors:
                rec_term = App(rec_term, m)
            for ia in index_args:
                rec_term = App(rec_term, ia)
            rec_term = App(rec_term, scrut_e)
            return rec_term, subgoals_out

        if kind == "induction":
            # Like `cases`, but with a *dependent* motive: each subgoal's
            # type is G with the scrutinee replaced by the ctor pattern,
            # and each IH has type `motive(rec_field)` (i.e. the goal
            # specialised at the recursive position).  This is what makes
            # induction useful — non-dependent cases would leave the goal
            # as the abstract `G` in every branch, useless for real proofs.
            _, expr, _bvar_stack = tac
            expr_r = _resolve_bvars(expr, ctx)
            scrut_e, scrut_ty = self.elab(expr_r, None, ctx)
            if not isinstance(scrut_e, FVar):
                raise ElabError(
                    f"induction: scrutinee must be a local hypothesis "
                    f"(FVar); got {show_expr(scrut_e)}. "
                    f"For arbitrary expressions, generalise first or use "
                    f"`cases`.")
            scrut_ty_w = self.kernel.whnf(
                self.mctx.instantiate(scrut_ty), ctx)
            head, ind_args = _spine(scrut_ty_w)
            if not isinstance(head, Const) or not self.env.has(head.name):
                raise ElabError(
                    f"induction: scrutinee type is not an inductive: "
                    f"{show_expr(scrut_ty_w)}")
            decl = self.env.get(head.name)
            if not isinstance(decl, Inductive):
                raise ElabError(
                    f"induction: {head.name} is not an inductive")
            rec_decl = self.env.get(decl.recursor_name)
            n_params = decl.num_params
            n_indices = decl.num_indices
            param_args = ind_args[:n_params]
            index_args = ind_args[n_params:n_params + n_indices]
            # For indexed inductives, require all index args in the
            # scrutinee's type to be FVars — we abstract them into the
            # motive's binders.  Concrete index args would need index
            # unification (generate Eq-hypotheses bridging the concrete
            # index to the constructor's index pattern); not done here.
            if n_indices > 0:
                for ia in index_args:
                    if not isinstance(ia, FVar):
                        raise ElabError(
                            f"induction: indexed inductive {decl.name} "
                            f"with non-FVar index {show_expr(ia)} not "
                            f"supported (index unification not done)")
            ind_lvls = head.levels
            G = self.mctx.instantiate(goal)
            # Build ind_applied with the original FVars (params and the
            # index FVars from the scrutinee's type).  We then `close`
            # those FVars one at a time as we add binders OUTSIDE — close
            # both walks into the existing dom and into the body and
            # shifts BVars consistently, so we get correct depth-correct
            # references.  (Pre-placing BVars in ind_applied gets shifted
            # by close and ends up out of bounds.)
            ind_applied: Expr = Const(decl.name, ind_lvls)
            for pa in param_args:
                ind_applied = App(ind_applied, pa)
            for ia in index_args:
                ind_applied = App(ind_applied, ia)
            # Build motive body: close G over the scrutinee FVar first,
            # then wrap with the scrut Lam.  After that, for each index
            # (last-to-first), close the index FVar (close descends the
            # existing Lams and increments cutoff) and wrap with the
            # index Lam.
            body = close(G, scrut_e.name, 0)
            motive = Lam(scrut_e.name, ind_applied, body)
            if n_indices > 0:
                ind_ty = inst_levels(decl.type_, decl.level_params, ind_lvls)
                for pa in param_args:
                    if not isinstance(ind_ty, Pi):
                        raise ElabError(
                            f"induction: {decl.name} has bad inductive type")
                    ind_ty = subst_bvar(ind_ty.body, 0, pa)
                index_types: list = []
                cur_ty = ind_ty
                for _ in range(n_indices):
                    if not isinstance(cur_ty, Pi):
                        raise ElabError(
                            f"induction: {decl.name} has bad inductive type")
                    index_types.append(cur_ty.dom)
                    cur_ty = cur_ty.body
                for i in reversed(range(n_indices)):
                    motive = close(motive, index_args[i].name, 0)
                    motive = Lam(f"_i{i}", index_types[i], motive)
            G_ty_w = self.kernel.whnf(
                self.mctx.instantiate(self._infer_elaborated(G, ctx)),
                ctx)
            if not isinstance(G_ty_w, Sort):
                raise ElabError(
                    f"induction: goal's type isn't a Sort: "
                    f"{show_expr(G_ty_w)}")
            v_level = G_ty_w.level

            # Pull out motive_body for the apply_motive helper.  It lives
            # under n_indices + 1 Lams; its BVars 0 .. n_indices are the
            # motive's own binders (BVar(0) = scrut, BVar(n_indices) = i_0),
            # everything BVar >= n_indices+1 references outer ctx.
            motive_body = motive
            for _ in range(n_indices + 1):
                motive_body = motive_body.body

            def apply_motive(idx_vals: list, scrut_val: Expr,
                              depth: int) -> Expr:
                """motive applied to (idx_vals[0], …, idx_vals[n-1], scrut_val)
                inside `depth` extra binders.  Shift motive_body's outer-ctx
                BVars by `depth`, then substitute the motive's own binders
                (BVar(0)=scrut, then the indices last-to-first)."""
                shifted = shift(motive_body, depth, n_indices + 1)
                result = subst_bvar(shifted, 0, scrut_val)
                # After subst, the n_indices remaining motive-binder BVars
                # are at positions 0 .. n_indices-1, corresponding to
                # i_{n-1}, i_{n-2}, …, i_0.  Substitute innermost first.
                for i in reversed(range(n_indices)):
                    result = subst_bvar(result, 0, idx_vals[i])
                return result

            ctx_snap = tuple(ctx.entries)
            minors: list = []
            subgoals_out: list = []
            for ctor_name in decl.constructor_names:
                cd = self.env.get(ctor_name)
                ct = inst_levels(cd.type_, cd.level_params, ind_lvls)
                for pa in param_args:
                    if not isinstance(ct, Pi):
                        raise ElabError(
                            f"induction: bad ctor type for {ctor_name}")
                    ct = subst_bvar(ct.body, 0, pa)
                field_types: list = []
                ctor_ret = ct
                for _ in range(cd.num_fields):
                    if not isinstance(ctor_ret, Pi):
                        raise ElabError(
                            f"induction: bad ctor type for {ctor_name}")
                    field_types.append(ctor_ret.dom)
                    ctor_ret = ctor_ret.body
                # ctor_ret is now `Ind params ctor_index_patterns(field_BVars)`.
                # Its BVars index fields in the ctor's Pi convention: after
                # all n_fields binders, BVar(0) = last field, BVar(j) = field
                # (n_fields - 1 - j).  Extract the index args.
                ret_head, ret_args = _spine(ctor_ret)
                if not (isinstance(ret_head, Const)
                        and ret_head.name == decl.name):
                    raise ElabError(
                        f"induction: ctor {ctor_name} return type has "
                        f"unexpected head {show_expr(ret_head)}")
                ctor_index_patterns = ret_args[n_params:n_params + n_indices]
                rec_rule = next(
                    (r for r in rec_decl.rules
                     if r.ctor_name == ctor_name), None)
                rec_positions = (rec_rule.rec_arg_positions
                                 if rec_rule else ())
                rec_index_templates = (rec_rule.rec_index_templates
                                       if rec_rule else ())
                n_fields = cd.num_fields
                n_rec = len(rec_positions)
                # Build the minor type innermost-first.
                # Inside the innermost body we are at depth n_fields + n_rec
                # extra binders beyond the outer ctx.  Fields are at
                # BVar(n_fields-1-i + n_rec); IHs at BVar(n_rec-1-k_idx).
                ctor_app: Expr = Const(ctor_name, ind_lvls)
                for pa in param_args:
                    ctor_app = App(ctor_app, shift(pa, n_fields + n_rec))
                for i in range(n_fields):
                    ctor_app = App(ctor_app,
                                   BVar(n_fields - 1 - i + n_rec))
                # The ctor's index patterns reference field BVars in the
                # ctor's own Pi convention (where field i is at BVar
                # (n_fields-1-i)).  In our minor's innermost context the
                # same fields live n_rec deeper, so shift by n_rec.
                ctor_idx_vals_inner = [shift(pat, n_rec)
                                       for pat in ctor_index_patterns]
                minor_ty = apply_motive(ctor_idx_vals_inner, ctor_app,
                                         n_fields + n_rec)
                for k_idx in reversed(range(n_rec)):
                    rec_field_pos = rec_positions[k_idx]
                    rec_field_bvar = BVar(
                        n_fields - 1 - rec_field_pos + k_idx)
                    # rec_index_templates use the env_no_rec convention:
                    # env = params ++ motives ++ minors ++ fields, so
                    # BVar(j) for j < n_fields references field
                    # (n_fields - 1 - j) (last-field-first).  In our IH
                    # context (depth n_fields + k_idx), the same fields
                    # are k_idx deeper than at the env_no_rec base.
                    if n_indices > 0:
                        ih_idx_vals = [shift(t, k_idx)
                                       for t in rec_index_templates[k_idx]]
                    else:
                        ih_idx_vals = []
                    ih_ty = apply_motive(ih_idx_vals, rec_field_bvar,
                                          n_fields + k_idx)
                    minor_ty = Pi(f"ih{k_idx}", ih_ty, minor_ty)
                for j in reversed(range(n_fields)):
                    minor_ty = Pi(f"f{j}", field_types[j], minor_ty)
                m = self.mctx.fresh(minor_ty)
                minors.append(m)
                subgoals_out.append((m.id, ctx_snap))
            rec_lvls: list = []
            for lp_name in rec_decl.level_params:
                if lp_name == rec_decl.motive_universe_param:
                    rec_lvls.append(v_level)
                else:
                    idx = decl.level_params.index(lp_name)
                    rec_lvls.append(ind_lvls[idx])
            rec_term: Expr = Const(rec_decl.name, tuple(rec_lvls))
            for pa in param_args:
                rec_term = App(rec_term, pa)
            rec_term = App(rec_term, motive)
            for m in minors:
                rec_term = App(rec_term, m)
            for ia in index_args:
                rec_term = App(rec_term, ia)
            rec_term = App(rec_term, scrut_e)
            return rec_term, subgoals_out

        if kind == "rewrite":
            _, expr, _bvar_stack = tac
            expr_r = _resolve_bvars(expr, ctx)
            h_elab, h_ty = self.elab(expr_r, None, ctx)
            h_ty_w = self.kernel.whnf(
                self.mctx.instantiate(h_ty), ctx)
            head, args = _spine(h_ty_w)
            if not (isinstance(head, Const) and head.name == "Eq"
                    and len(args) == 3):
                raise ElabError(
                    f"rewrite: hypothesis must have type `Eq α a b`, "
                    f"got {show_expr(h_ty_w)}")
            α, a, b = args
            u_level = head.levels[0]
            # β-normalise the goal so motive-applications coming out of a
            # recursor minor (shape: `(λk. P k) (ctor args)`) become the
            # literal `P[ctor args / k]` that structural search can scan.
            G = _beta_norm(self.mctx.instantiate(goal))
            # Determine v from the goal's type — the motive's body IS the
            # goal (modulo the abstraction), so its level is the goal's.
            G_ty_w = self.kernel.whnf(
                self.mctx.instantiate(self._infer_elaborated(G, ctx)),
                ctx)
            if not isinstance(G_ty_w, Sort):
                raise ElabError(
                    f"rewrite: goal's type is not a Sort: "
                    f"{show_expr(G_ty_w)}")
            v_level = G_ty_w.level
            # For v1 we only support `a` being a closed expression that
            # appears in G by structural equality.  Walk G replacing each
            # such occurrence with BVar(1) (which will be the motive's
            # `a'` binder).
            G_shifted = shift(G, 2)
            replaced, occurred = _replace_term(
                G_shifted, shift(a, 2), BVar(1))
            if not occurred:
                raise ElabError(
                    f"rewrite: LHS {show_expr(a)} not found in goal "
                    f"{show_expr(G)}")
            motive_body = replaced                      # under 2 Lams: a', _hp
            inner_lam = Lam(
                "_hp",
                # `Eq.{u} α b a'` at outer-Lam scope (one binder)
                App(App(App(Const("Eq", (u_level,)), shift(α, 1)),
                        shift(b, 1)), BVar(0)),
                motive_body)
            motive = Lam("a'", α, inner_lam)
            sym_h = App(App(App(App(Const("Eq.symm", (u_level,)), α), a),
                            b), h_elab)
            # New subgoal type: G with `a` replaced by `b` (rewritten goal).
            new_goal, _ = _replace_term(G, a, b)
            sub_meta = self.mctx.fresh(new_goal)
            term = App(App(App(App(App(App(
                Const("Eq.rec", (u_level, v_level)),
                α), b), motive), sub_meta), a), sym_h)
            ctx_snap = tuple(ctx.entries)
            return term, [(sub_meta.id, ctx_snap)]

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
                 ctx: LocalCtx) -> Tuple[Expr, list]:
        """Run a tactic sequence with focused-goal semantics.

        State:
        - One focused goal (the "main" goal initially; each subgoal in
          turn afterward).
        - A stack of focused intros: each adds an FVar to `ctx` and
          shrinks the focused goal by one Π.
        - A queue of pending subgoals (each carries a ctx snapshot from
          its creation site).

        Each tactic acts on the focused goal.  `intro` peels a Π off it.
        Any other tactic produces a term that solves the focused goal:
        if focused goal is the MAIN goal we defer wrapping its intros to
        the very end (so meta assignments from later subgoals can refer
        to those intros by FVar and be closed in a single final walk);
        for subgoals we wrap focused intros into Lams immediately.
        Subgoals produced by a tactic are prepended (depth-first)."""
        if not tacs:
            raise ElabError("empty tactic sequence")
        initial_entries = list(ctx.entries)
        focused_is_main = True
        focused_meta_id: Optional[int] = None
        focused_goal = goal
        focused_intros: List[Tuple[str, Expr, str]] = []
        # Main goal's intros are pushed onto ctx but NOT popped until the
        # very end — that way subgoal-solving terms can reference them as
        # FVars and the final close() unifies everything.
        main_intros: List[Tuple[str, Expr, str]] = []
        main_term: Optional[Expr] = None
        pending: List[Tuple[int, Expr, tuple]] = []
        # Subgoal-local intros that need to be Lam-wrapped + closed once
        # all subgoals are solved.  We can't wrap immediately because the
        # subgoal-solving term may contain unresolved inner metas, and
        # close() only walks the surface — it doesn't reach into a Meta
        # node, so FVars that get substituted in later would slip out
        # unclosed.  Each entry is (meta_id, intros, raw_term).  Processed
        # in reverse chronological order at end so inner deferred wraps
        # resolve before outer ones reference them.
        deferred_subgoal_wraps: List[
            Tuple[int, List[Tuple[str, Expr, str]], Expr]] = []
        try:
            for tac in tacs:
                if focused_goal is None:
                    raise ElabError(
                        f"extra tactic with no remaining goals: {tac[0]!r}")
                if tac[0] == "intro":
                    name = tac[1]
                    goal_w = self.kernel.whnf(
                        self.mctx.instantiate(focused_goal), ctx)
                    if not isinstance(goal_w, Pi):
                        raise ElabError(
                            f"intro {name!r}: focused goal is not a Π, got "
                            f"{show_expr(goal_w)}")
                    dom = goal_w.dom
                    fv = ctx.push(name, dom)
                    focused_intros.append((name, dom, fv))
                    focused_goal = open_(goal_w.body, FVar(fv, dom))
                    continue
                if tac[0] == "revert":
                    # Anti-intro: find the named intro in focused_intros,
                    # check that no later intro's type depends on it
                    # (otherwise reverting would leave a dangling FVar
                    # reference), then pop it from focused_intros and ctx
                    # and wrap focused_goal with a Π binder.
                    name = tac[1]
                    target_idx = None
                    for i, (nm, _, _) in enumerate(focused_intros):
                        if nm == name:
                            target_idx = i
                    if target_idx is None:
                        raise ElabError(
                            f"revert: no intro named {name!r} in scope. "
                            f"revert only works on hypotheses introduced "
                            f"by `intro` in this tactic block; theorem "
                            f"binders cannot be reverted.")
                    (rev_name, rev_dom, rev_fv) = focused_intros[target_idx]
                    # Reject if any later intro depends on this FVar.
                    for nm2, dom2, _fv2 in focused_intros[target_idx + 1:]:
                        if _references_fvar(dom2, rev_fv):
                            raise ElabError(
                                f"revert: later hypothesis {nm2!r} depends "
                                f"on {name!r}; revert {nm2!r} first or "
                                f"reorder")
                    # Pop the corresponding ctx entry (not necessarily
                    # the last one — find by name).
                    pop_idx = None
                    for i in range(len(ctx.entries) - 1, -1, -1):
                        if ctx.entries[i][0] == rev_fv:
                            pop_idx = i
                            break
                    if pop_idx is None:
                        raise ElabError(
                            f"revert: ctx entry for {rev_fv!r} not found "
                            f"(internal error)")
                    del ctx.entries[pop_idx]
                    del focused_intros[target_idx]
                    focused_goal = Pi(
                        rev_name, rev_dom,
                        close(focused_goal, rev_fv, 0))
                    continue
                # Non-intro tactic: produce a term for the focused goal.
                term, sub_metas = self._run_tactic(tac, focused_goal, ctx)
                term = self.mctx.instantiate(term)
                if focused_is_main:
                    # Defer wrapping the main intros — leave them pushed
                    # so later subgoal solutions can use them as FVars.
                    main_intros = focused_intros[:]
                    main_term = term
                    focused_intros = []
                else:
                    if focused_intros:
                        # Defer the wrap.  We don't assign the meta yet;
                        # it stays unsolved until the post-seq processing
                        # loop below — at which point any inner metas
                        # have already been resolved, and instantiate +
                        # close together produce a fully-closed Lam.
                        deferred_subgoal_wraps.append(
                            (focused_meta_id, focused_intros[:], term))
                        focused_intros = []
                    else:
                        self.mctx.assign(focused_meta_id,
                                         self.mctx.instantiate(term))
                # Prepend new subgoals (depth-first).
                new_pending: List[Tuple[int, Expr, tuple]] = []
                for sub in sub_metas:
                    meta_id, sub_ctx_snap = _subgoal_unpack(sub, ctx)
                    if self.mctx.get(meta_id) is not None:
                        continue
                    meta_ty = self.mctx.instantiate(
                        self.mctx.get_type(meta_id))
                    new_pending.append((meta_id, meta_ty, sub_ctx_snap))
                pending = new_pending + pending
                while pending:
                    m_id, _ty, _snap = pending[0]
                    if self.mctx.get(m_id) is None:
                        break
                    pending.pop(0)
                if pending:
                    m_id, m_ty, m_snap = pending.pop(0)
                    focused_is_main = False
                    focused_meta_id = m_id
                    focused_goal = self.mctx.instantiate(m_ty)
                    ctx.entries[:] = list(m_snap)
                else:
                    focused_goal = None
            if focused_goal is not None:
                if focused_intros:
                    raise ElabError(
                        "tactic sequence ends with intro — needs a body")
                raise ElabError(
                    f"unsolved focused goal at end of seq: "
                    f"{show_expr(self.mctx.instantiate(focused_goal))}")
            if pending:
                m_id, m_ty, _ = pending[0]
                raise ElabError(
                    f"unsolved subgoal at end of seq: "
                    f"{show_expr(self.mctx.instantiate(m_ty))}")
            if main_term is None:
                raise ElabError("seq has only intros, no body tactic")
            # Process deferred subgoal-local intro wraps in reverse order
            # (inner-first), so each outer entry's term has its inner
            # metas already resolved by the time we instantiate + close.
            for meta_id, intros, term in reversed(deferred_subgoal_wraps):
                term = self.mctx.instantiate(term)
                for name, dom, fv in reversed(intros):
                    term = Lam(name, dom,
                               close(self.mctx.instantiate(term), fv))
                self.mctx.assign(meta_id, self.mctx.instantiate(term))
            # Final wrap: instantiate fully, then close main's intros.
            result = self.mctx.instantiate(main_term)
            for name, dom, fv in reversed(main_intros):
                result = Lam(name, dom, close(result, fv))
            return result, []
        finally:
            ctx.entries[:] = initial_entries

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
    if kind == "theorem":
        # `example` becomes "theorem" in the parser; both produce a Theorem
        # decl, which the kernel and emitter treat as opaque (no δ-unfold).
        ker.add_theorem(Theorem(
            name=name, level_params=level_params,
            type_=ty_elab, value=body_e))
        return
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
