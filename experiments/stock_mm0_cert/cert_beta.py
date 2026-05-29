"""Layer 2: beta-conversion certificates (a certifying evaluator).

Builds on cert.py (Layer 1).  Two pieces:

  prove_type(t, ctx, env) -> (type, proof)
      a typing certifier for the lambda fragment + the nat constants.
      `ctx` is a list of (name, type) for lambda binders (innermost LAST);
      `env` maps hypothesis-typed free vars to (type, proof-name), e.g.
      {"a": (Var("A"), "ha")}.  Weakening is emitted automatically as
      stacked `ty_cons`.

  prove_whnf(t, ctx, env) -> (nf, conv | None)
      leftmost-outermost weak-head reduction.  Emits `conv_beta` for each
      contracted redex (with the Layer-1 substitution proof), wraps in
      app-congruence (`conv_ty_ndapp`) when it reduces inside an application
      head, and chains everything with `conv_trans`.  `None` means "already
      in whnf" (an identity conversion we simply omit).

As with Layer 1, every binder is globally fresh, so no capture / DV issue
ever arises -- the alpha bookkeeping that blocked hand-authoring is gone.
"""
from __future__ import annotations
import re
from cert import Term, Sort, Var, Const, App, Lam, Pi, Imp, NatRec, pp, fv, prove_subst


def _wrap(proof: str, k: int, ctor: str) -> str:
    """Apply unary axiom `ctor` k times around `proof` (e.g. weakening)."""
    return f"({ctor} " * k + proof + ")" * k


def conv_trans(c1, c2):
    """conv_trans, dropping identity (None) conversions."""
    if c1 is None: return c2
    if c2 is None: return c1
    return f"(conv_trans {c1} {c2})"


# ----------------------------------------------------------------------
# typing certifier
# ----------------------------------------------------------------------
def prove_type_const(t: Const, ctx):
    k = len(ctx)                       # weaken from nil up to the current ctx
    if t.name == "nat":
        return Const("Type"), _wrap("ty_nat", k, "ty_cons")
    if t.name == "nat_zero":
        return Const("nat"), _wrap("ty_nat_zero", k, "ty_cons")
    if t.name == "nat_succ":
        return Imp(Const("nat"), Const("nat")), _wrap("ty_nat_succ", k, "ty_cons")
    raise KeyError(f"no typing rule for constant {t.name!r}")


def prove_type(t: Term, ctx, env):
    if isinstance(t, Var):
        for i in range(len(ctx) - 1, -1, -1):       # innermost first
            if ctx[i][0] == t.name:
                return ctx[i][1], _wrap("ty_var", len(ctx) - 1 - i, "ty_cons")
        if t.name in env:                            # hypothesis-typed var
            ty, p0 = env[t.name]
            return ty, _wrap(p0, len(ctx), "ty_cons")
        raise KeyError(f"untyped variable {t.name!r}")
    if isinstance(t, App):
        tf, pf = prove_type(t.fn, ctx, env)
        _ta, pa = prove_type(t.arg, ctx, env)
        if isinstance(tf, Imp):                       # non-dependent: A -> B
            return tf.cod, f"(ty_ndapp {pf} {pa})"
        if isinstance(tf, Pi):                        # dependent: B[arg/x]
            res, ps = prove_subst(tf.body, t.arg, tf.var)
            return res, f"(ty_app {pf} {pa} {ps})"
        raise TypeError(f"applying non-function of type {pp(tf)}")
    if isinstance(t, Lam):
        tb, pb = prove_type(t.body, ctx + [(t.var, t.ty)], env)
        return Pi(t.var, t.ty, tb), f"(ty_lambda {pb})"
    if isinstance(t, Const):
        return prove_type_const(t, ctx)
    raise TypeError(t)


# ----------------------------------------------------------------------
# certifying whnf reducer
# ----------------------------------------------------------------------
def _app_cong(f, fconv, arg, ctx, env):
    """Congruence: from (f |= fnf) build (f @ arg |= fnf @ arg)."""
    _fty, fproof = prove_type(f, ctx, env)
    _aty, aproof = prove_type(arg, ctx, env)
    return (f"(and_right (conv_ty_ndapp (conv_ty_l {fproof} {fconv}) "
            f"(conv_ty_refl {aproof})))")


def prove_whnf(t: Term, ctx, env):
    if not isinstance(t, App):
        return t, None                               # already whnf
    fnf, fconv = prove_whnf(t.fn, ctx, env)
    if isinstance(fnf, Lam):                          # beta-redex
        x, T, body = fnf.var, fnf.ty, fnf.body
        res0, psub = prove_subst(body, t.arg, x)
        _bt, bproof = prove_type(body, ctx + [(x, T)], env)
        _at, aproof = prove_type(t.arg, ctx, env)
        beta = f"(conv_beta {bproof} {aproof} {psub})"
        head = _app_cong(t.fn, fconv, t.arg, ctx, env) if fconv else None
        resnf, resconv = prove_whnf(res0, ctx, env)  # keep reducing
        return resnf, conv_trans(head, conv_trans(beta, resconv))
    # neutral head: application is in whnf
    if fconv:
        return App(fnf, t.arg), _app_cong(t.fn, fconv, t.arg, ctx, env)
    return App(fnf, t.arg), None


# ----------------------------------------------------------------------
# proof-node accounting + theorem emission
# ----------------------------------------------------------------------
_AX = re.compile(r'[A-Za-z_]\w*')
_VOCAB = {"subst_nf", "subst_var", "subst_app", "subst_lambda", "subst_Pi",
          "conv_beta", "conv_trans", "conv_ty_l", "conv_ty_refl",
          "conv_ty_ndapp", "and_right",
          "ty_var", "ty_cons", "ty_ndapp", "ty_app", "ty_lambda",
          "ty_nat", "ty_nat_zero", "ty_nat_succ"}

def proof_nodes(proof: str) -> int:
    return sum(1 for tok in _AX.findall(proof) if tok in _VOCAB)
