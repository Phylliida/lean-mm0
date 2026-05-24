"""CIC type checker with a derivation-recording mode.

The checker is a syntactic mirror of the inference rules of CIC.
When `record=True` it returns a `Deriv` tree alongside the inferred type;
the emitter walks that tree to produce MM0 proof scripts.

Reduction supports β, δ (unfold definitions), ζ (let), ι (recursors).
Definitional equality is decided structurally over weak-head normal forms.
The implementation is straightforward; correctness is more important than
performance.
"""
from __future__ import annotations
from dataclasses import dataclass, field
from typing import Tuple, List, Optional, Union
import itertools

from .levels import (
    Level, LZero, LSucc, LMax, LIMax, LParam,
    level_zero, level_succ, level_max, level_imax,
    equiv as lvl_equiv, normalize as lvl_normalize, show as show_level,
)
from .expr import (
    Expr, Sort, BVar, FVar, Const, App, Lam, Pi, Let,
    shift, subst_bvar, beta, open_, close, inst_levels, show as show_expr,
    app_many,
)
from .env import (
    Env, Definition, Axiom, Constructor, Recursor, Inductive, RecursorRule,
)


# ---------------- derivation trees ----------------

@dataclass
class Deriv:
    rule: str
    concl_term: Expr
    concl_type: Expr
    premises: Tuple["Deriv", ...] = ()
    eqs: Tuple["EqDeriv", ...] = ()
    extra: dict = field(default_factory=dict)


@dataclass
class EqDeriv:
    rule: str
    lhs: Expr
    rhs: Expr
    premises: Tuple["EqDeriv", ...] = ()
    extra: dict = field(default_factory=dict)


# ---------------- context ----------------

@dataclass
class LocalCtx:
    """Telescope of free variables introduced by entering binders.
    Each entry is (name, type, value-or-None)."""
    entries: List[Tuple[str, Expr, Optional[Expr]]] = field(default_factory=list)

    def push(self, name: str, type_: Expr, value: Optional[Expr] = None) -> str:
        # ensure unique
        n = name
        i = 0
        existing = {e[0] for e in self.entries}
        while n in existing:
            i += 1
            n = f"{name}#{i}"
        self.entries.append((n, type_, value))
        return n

    def pop(self) -> None:
        self.entries.pop()

    def lookup(self, name: str) -> Tuple[Expr, Optional[Expr]]:
        for n, t, v in self.entries:
            if n == name:
                return t, v
        raise KeyError(name)


# ---------------- typing errors ----------------

class TypeError_(Exception):
    pass


# ---------------- the kernel ----------------

class Kernel:
    def __init__(self, env: Env, record: bool = False) -> None:
        self.env = env
        self.record = record

    # ------------- reduction -------------

    def whnf(self, e: Expr, ctx: LocalCtx, trace: Optional[List["EqDeriv"]] = None) -> Expr:
        """Weak head normal form.  If `trace` is given, every reduction step
        appends an EqDeriv whose lhs/rhs witnesses one step of definitional
        equality."""
        cur = e
        while True:
            if isinstance(cur, FVar):
                _, val = ctx.lookup(cur.name)
                if val is None:
                    return cur
                if trace is not None:
                    trace.append(EqDeriv("zeta-var", cur, val))
                cur = val
                continue
            if isinstance(cur, Let):
                nxt = subst_bvar(cur.body, 0, cur.value)
                if trace is not None:
                    trace.append(EqDeriv("zeta", cur, nxt))
                cur = nxt
                continue
            if isinstance(cur, Const):
                decl = self.env.get(cur.name)
                if isinstance(decl, Definition):
                    nxt = inst_levels(decl.value, decl.level_params, cur.levels)
                    if trace is not None:
                        trace.append(EqDeriv("delta", cur, nxt, extra={"name": cur.name}))
                    cur = nxt
                    continue
                return cur
            if isinstance(cur, App):
                fn = self.whnf(cur.fn, ctx, trace)
                if isinstance(fn, Lam):
                    nxt = beta(fn.body, cur.arg)
                    if trace is not None:
                        trace.append(EqDeriv("beta", App(fn, cur.arg), nxt))
                    cur = nxt
                    continue
                # ι-reduction: head is a recursor applied to a constructor
                ired = self.try_iota(fn, cur.arg, trace, ctx)
                if ired is not None:
                    cur = ired
                    continue
                return App(fn, cur.arg) if fn is not cur.fn else cur
            return cur

    def try_iota(self, fn: Expr, arg: Expr,
                 trace: Optional[List[EqDeriv]],
                 ctx: Optional[LocalCtx] = None) -> Optional[Expr]:
        """If `fn arg` is a fully-applied recursor over a constructor head,
        rewrite by the recursor's ι-rule.  Returns the reduct, or None."""
        # collect spine
        spine = [arg]
        head = fn
        while isinstance(head, App):
            spine.insert(0, head.arg)
            head = head.fn
        if not isinstance(head, Const):
            return None
        decl = self.env.get(head.name) if self.env.has(head.name) else None
        if not isinstance(decl, Recursor):
            return None
        total = decl.num_params + decl.num_motives + decl.num_minors + decl.num_indices + 1
        if len(spine) < total:
            return None
        major_idx = decl.num_params + decl.num_motives + decl.num_minors + decl.num_indices
        major = spine[major_idx]
        # whnf the major so definitions / let-bindings are exposed and
        # the constructor head becomes visible
        major_w = self.whnf(major, ctx if ctx is not None else LocalCtx())
        m_spine = []
        m_head = major_w
        while isinstance(m_head, App):
            m_spine.insert(0, m_head.arg)
            m_head = m_head.fn
        if not isinstance(m_head, Const):
            return None
        ctor_decl = self.env.get(m_head.name) if self.env.has(m_head.name) else None
        if not isinstance(ctor_decl, Constructor) or ctor_decl.inductive != decl.inductive:
            return None
        rule = next((r for r in decl.rules if r.ctor_name == ctor_decl.name), None)
        if rule is None:
            return None
        # the ctor's leading args are its own params (may be fewer than the
        # recursor's leading-arg count for things like Quot.lift)
        np_ctor = rule.n_ctor_params_override if rule.n_ctor_params_override >= 0 \
                  else ctor_decl.num_params
        ctor_args = m_spine
        if len(ctor_args) < np_ctor + ctor_decl.num_fields:
            return None
        field_args = ctor_args[np_ctor:np_ctor + ctor_decl.num_fields]

        # env_subst uses the *recursor*'s params (which may include extras
        # like β for Quot.lift), not the ctor's params.
        rec_params_args = spine[:decl.num_params]
        rec_motives_args = spine[decl.num_params:decl.num_params + decl.num_motives]
        rec_minors_args = spine[decl.num_params + decl.num_motives:
                                decl.num_params + decl.num_motives + decl.num_minors]

        # recursor head for rec_results
        rec_head: Expr = head
        for a in list(rec_params_args) + list(rec_motives_args) + list(rec_minors_args):
            rec_head = App(rec_head, a)

        # env-without-rec_results, used to instantiate index templates
        env_no_rec_kernel = list(rec_params_args) + list(rec_motives_args) \
                          + list(rec_minors_args) + list(field_args)

        rec_results: List[Expr] = []
        for k, pos in enumerate(rule.rec_arg_positions):
            sub_major = field_args[pos]
            if decl.num_indices == 0:
                sub_indices: List[Expr] = []
            else:
                if k >= len(rule.rec_index_templates):
                    return None
                tpl = rule.rec_index_templates[k]
                if len(tpl) != decl.num_indices:
                    return None
                sub_indices = []
                for t in tpl:
                    inst = t
                    for v in reversed(env_no_rec_kernel):
                        inst = subst_bvar(inst, 0, v)
                    sub_indices.append(inst)
            call = rec_head
            for idx_e in sub_indices:
                call = App(call, idx_e)
            call = App(call, sub_major)
            rec_results.append(call)

        # rule.rhs_template uses BVars in the env_subst convention.
        env_subst = list(rec_params_args) + list(rec_motives_args) \
                  + list(rec_minors_args) + list(field_args) + list(rec_results)
        rhs = rule.rhs_template
        # substitute outermost-first.  rhs_template uses BVars; the convention
        # used by inductive.py is BVar(i) with i=0 the *last* in env_subst.
        for i, v in enumerate(reversed(env_subst)):
            rhs = subst_bvar(rhs, 0, v)
            # subst_bvar shifts inner indices; this loop is equivalent to a
            # simultaneous substitution because each call collapses BVar 0.
        if trace is not None:
            trace.append(EqDeriv("iota", app_many(fn, arg), rhs,
                                 extra={"recursor": decl.name, "ctor": ctor_decl.name}))
        return rhs

    # ------------- definitional equality -------------

    def def_eq(self, a: Expr, b: Expr, ctx: LocalCtx,
               trace: Optional[List[EqDeriv]] = None) -> bool:
        # short-circuit
        if a == b:
            if trace is not None:
                trace.append(EqDeriv("refl", a, b))
            return True

        # try structural equality on whnf
        local: List[EqDeriv] = []
        wa = self.whnf(a, ctx, local)
        local_b: List[EqDeriv] = []
        wb = self.whnf(b, ctx, local_b)

        if isinstance(wa, Sort) and isinstance(wb, Sort):
            if lvl_equiv(wa.level, wb.level):
                if trace is not None:
                    trace.extend(local)
                    trace.append(EqDeriv("sort-eq", wa, wb))
                    trace.extend(reversed([EqDeriv("sym-step", e.rhs, e.lhs) for e in local_b]))
                return True
            return False
        if isinstance(wa, BVar) and isinstance(wb, BVar):
            return wa.idx == wb.idx
        if isinstance(wa, FVar) and isinstance(wb, FVar):
            return wa.name == wb.name
        if isinstance(wa, Const) and isinstance(wb, Const):
            if wa.name == wb.name and len(wa.levels) == len(wb.levels):
                ok = all(lvl_equiv(x, y) for x, y in zip(wa.levels, wb.levels))
                if ok and trace is not None:
                    trace.extend(local)
                    trace.append(EqDeriv("const-eq", wa, wb))
                    trace.extend(reversed([EqDeriv("sym-step", e.rhs, e.lhs) for e in local_b]))
                return ok
            return False
        if isinstance(wa, App) and isinstance(wb, App):
            ok_fn = self.def_eq(wa.fn, wb.fn, ctx)
            ok_arg = self.def_eq(wa.arg, wb.arg, ctx)
            if ok_fn and ok_arg and trace is not None:
                trace.extend(local)
                trace.append(EqDeriv("app-cong", wa, wb))
                trace.extend(reversed([EqDeriv("sym-step", e.rhs, e.lhs) for e in local_b]))
            return ok_fn and ok_arg
        if isinstance(wa, Pi) and isinstance(wb, Pi):
            if not self.def_eq(wa.dom, wb.dom, ctx):
                return False
            fv = ctx.push(wa.binder, wa.dom)
            try:
                if not self.def_eq(open_(wa.body, FVar(fv, wa.dom)),
                                   open_(wb.body, FVar(fv, wa.dom)), ctx):
                    return False
            finally:
                ctx.pop()
            if trace is not None:
                trace.extend(local)
                trace.append(EqDeriv("pi-cong", wa, wb))
                trace.extend(reversed([EqDeriv("sym-step", e.rhs, e.lhs) for e in local_b]))
            return True
        if isinstance(wa, Lam) and isinstance(wb, Lam):
            if not self.def_eq(wa.dom, wb.dom, ctx):
                return False
            fv = ctx.push(wa.binder, wa.dom)
            try:
                if not self.def_eq(open_(wa.body, FVar(fv, wa.dom)),
                                   open_(wb.body, FVar(fv, wa.dom)), ctx):
                    return False
            finally:
                ctx.pop()
            if trace is not None:
                trace.extend(local)
                trace.append(EqDeriv("lam-cong", wa, wb))
                trace.extend(reversed([EqDeriv("sym-step", e.rhs, e.lhs) for e in local_b]))
            return True
        # η for lambdas: λx. f x ≡ f
        if isinstance(wa, Lam) and not isinstance(wb, Lam):
            return self._eta_eq(wa, wb, ctx, trace)
        if isinstance(wb, Lam) and not isinstance(wa, Lam):
            return self._eta_eq(wb, wa, ctx, trace)
        return False

    def _eta_eq(self, lam: Lam, other: Expr, ctx: LocalCtx,
                trace: Optional[List[EqDeriv]]) -> bool:
        # check  lam ≡ λx. other x
        synthesized = Lam(lam.binder, lam.dom,
                          App(shift(other, 1), BVar(0)))
        return self.def_eq(lam, synthesized, ctx, trace)

    # ------------- type inference -------------

    def infer(self, e: Expr, ctx: LocalCtx) -> Tuple[Expr, Optional[Deriv]]:
        rec = self.record

        if isinstance(e, Sort):
            ty = Sort(level_succ(e.level))
            d = Deriv("ht_sort", e, ty) if rec else None
            return ty, d

        if isinstance(e, BVar):
            raise TypeError_(f"unbound BVar {e.idx} reached infer")

        if isinstance(e, FVar):
            ty, _ = ctx.lookup(e.name)
            d = Deriv("ht_fvar", e, ty, extra={"name": e.name}) if rec else None
            return ty, d

        if isinstance(e, Const):
            decl = self.env.get(e.name)
            params = getattr(decl, "level_params", ())
            type_ = getattr(decl, "type_", None)
            if type_ is None:
                raise TypeError_(f"declaration {e.name} has no type")
            if len(params) != len(e.levels):
                raise TypeError_(f"const {e.name} expects {len(params)} level args, got {len(e.levels)}")
            ty = inst_levels(type_, params, e.levels)
            d = Deriv("ht_const", e, ty, extra={"name": e.name, "levels": e.levels}) if rec else None
            return ty, d

        if isinstance(e, App):
            tf, df = self.infer(e.fn, ctx)
            tf_w = self.whnf(tf, ctx)
            if not isinstance(tf_w, Pi):
                raise TypeError_(f"function expected, got {show_expr(tf_w)} for {show_expr(e.fn)}")
            ta, da = self.infer(e.arg, ctx)
            eq_trace: List[EqDeriv] = []
            if not self.def_eq(ta, tf_w.dom, ctx, eq_trace):
                raise TypeError_(
                    f"argument type mismatch:\n"
                    f"  expected {show_expr(tf_w.dom)}\n"
                    f"  got      {show_expr(ta)}"
                )
            ty = subst_bvar(tf_w.body, 0, e.arg)
            d = None
            if rec:
                d = Deriv("ht_app", e, ty, premises=(df, da), eqs=tuple(eq_trace))
            return ty, d

        if isinstance(e, Lam):
            tdom, ddom = self.infer(e.dom, ctx)
            tdom_w = self.whnf(tdom, ctx)
            if not isinstance(tdom_w, Sort):
                raise TypeError_(f"domain of λ must be a type, got {show_expr(tdom)}")
            fv = ctx.push(e.binder, e.dom)
            try:
                body_open = open_(e.body, FVar(fv, e.dom))
                tbody, dbody = self.infer(body_open, ctx)
                # close back to a Pi
                ty = Pi(e.binder, e.dom, close(tbody, fv))
            finally:
                ctx.pop()
            d = None
            if rec:
                d = Deriv("ht_lam", e, ty, premises=(ddom, dbody))
            return ty, d

        if isinstance(e, Pi):
            tdom, ddom = self.infer(e.dom, ctx)
            tdom_w = self.whnf(tdom, ctx)
            if not isinstance(tdom_w, Sort):
                raise TypeError_(f"domain of Π must be a type, got {show_expr(tdom)}")
            fv = ctx.push(e.binder, e.dom)
            try:
                tbody, dbody = self.infer(open_(e.body, FVar(fv, e.dom)), ctx)
                tbody_w = self.whnf(tbody, ctx)
                if not isinstance(tbody_w, Sort):
                    raise TypeError_(f"codomain of Π must be a type, got {show_expr(tbody)}")
                ty = Sort(level_imax(tdom_w.level, tbody_w.level))
            finally:
                ctx.pop()
            d = None
            if rec:
                d = Deriv("ht_pi", e, ty, premises=(ddom, dbody))
            return ty, d

        if isinstance(e, Let):
            ttype, dtype = self.infer(e.type_, ctx)
            ttype_w = self.whnf(ttype, ctx)
            if not isinstance(ttype_w, Sort):
                raise TypeError_(f"let-binding annotation must be a type")
            tval, dval = self.infer(e.value, ctx)
            if not self.def_eq(tval, e.type_, ctx):
                raise TypeError_("let-binding value/type mismatch")
            fv = ctx.push(e.binder, e.type_, e.value)
            try:
                tbody, dbody = self.infer(open_(e.body, FVar(fv, e.type_)), ctx)
                ty = subst_bvar(close(tbody, fv), 0, e.value)
            finally:
                ctx.pop()
            d = None
            if rec:
                d = Deriv("ht_let", e, ty, premises=(dtype, dval, dbody))
            return ty, d

        raise TypeError_(f"infer: unknown expression {e!r}")

    def check(self, e: Expr, expected: Expr, ctx: LocalCtx) -> Optional[Deriv]:
        got, d = self.infer(e, ctx)
        if self.def_eq(got, expected, ctx):
            return d
        # try reducing
        if self.def_eq(self.whnf(got, ctx), self.whnf(expected, ctx), ctx):
            return d
        raise TypeError_(
            f"type mismatch:\n"
            f"  expected {show_expr(expected)}\n"
            f"  got      {show_expr(got)}"
        )

    # ------------- declarations -------------

    def add_definition(self, d: Definition) -> Optional[Deriv]:
        # type-check the type, then the value
        ctx = LocalCtx()
        ttype, _ = self.infer(d.type_, ctx)
        if not isinstance(self.whnf(ttype, ctx), Sort):
            raise TypeError_(f"definition {d.name} has non-type type")
        deriv = self.check(d.value, d.type_, ctx)
        self.env.add(d)
        return deriv

    def add_axiom(self, a: Axiom) -> None:
        ctx = LocalCtx()
        ttype, _ = self.infer(a.type_, ctx)
        if not isinstance(self.whnf(ttype, ctx), Sort):
            raise TypeError_(f"axiom {a.name} has non-type type")
        self.env.add(a)
