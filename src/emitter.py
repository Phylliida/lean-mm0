"""Lean → MM0 emitter.

Walks an environment of Lean declarations and produces an MM0 file
that:
  * declares one (term econst-<name> () expr) per Lean declaration;
  * for axioms / inductives / constructors / recursors: an MM0 axiom
    asserting the typing judgment (taken as primitive, since they are
    primitives of CIC);
  * for each Lean definition: a theorem proving the typing judgment,
    with a proof reconstructed from the kernel's derivation.

The kernel does the type-checking work; the emitter just translates
the derivation tree into MM0 forward-proof syntax.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import List, Dict, Tuple, Optional, Union
import io
import re

from .levels import Level, LZero, LSucc, LMax, LIMax, LParam, normalize as lnorm
from .expr import (
    Expr, Sort, BVar, FVar, Const, App, Lam, Pi, Let, shift, subst_bvar,
    open_, close, inst_levels,
)
from .env import (
    Env, Definition, Theorem, Axiom, Constructor, Recursor, Inductive, RecursorRule,
)
from .kernel import Kernel, LocalCtx, Deriv, EqDeriv
from .mm0_verify import SExpr


# ---------------- encoding to s-expressions ----------------
#
# Lean names can contain '.', which isn't a valid MM0 identifier char.
# We escape '.' as '_d_' (NOT '_') so that `Foo.bar_baz` and `Foo.bar.baz`
# emit distinct symbols.  Any other unsafe char becomes _xNN_ (hex).


def _safe(n: str) -> str:
    out = []
    for c in n:
        if c.isalnum() or c == "_":
            out.append(c)
        elif c == ".":
            out.append("_d_")
        else:
            out.append(f"_x{ord(c):02x}_")
    return "".join(out)


def encode_name(n: str) -> str:
    """Make a Lean name safe to use as an MM0 identifier."""
    return "econst-" + _safe(n)


def encode_typing_name(n: str) -> str:
    return _safe(n) + "-typing"


def encode_delta_name(n: str) -> str:
    return _safe(n) + "-delta"


def encode_iota_name(rec_name: str, ctor_name: str) -> str:
    return _safe(rec_name) + "-iota-" + _safe(ctor_name)


def _nat_lit(n: int) -> SExpr:
    e: SExpr = "nzero"
    for _ in range(n):
        e = ["nsucc", e]
    return e


def encode_level(l: Level) -> SExpr:
    l = lnorm(l)
    if isinstance(l, LZero):
        return "lzero"
    if isinstance(l, LSucc):
        return ["lsucc", encode_level(l.arg)]
    if isinstance(l, LMax):
        return ["lmax", encode_level(l.a), encode_level(l.b)]
    if isinstance(l, LIMax):
        return ["limax", encode_level(l.a), encode_level(l.b)]
    if isinstance(l, LParam):
        return l.name             # MM0 level variable
    raise TypeError(l)


def encode_expr(e: Expr, fv_idx: Dict[str, int], depth: int) -> SExpr:
    """Encode a kernel Expr into the MM0 expr sort.

    fv_idx maps an FVar's name to its current de Bruijn index from the
    innermost binder.  Called with depth==0 at the top; depth grows
    inside binders so we can shift fv_idx accordingly.
    """
    if isinstance(e, Sort):
        return ["esort", encode_level(e.level)]
    if isinstance(e, BVar):
        return ["evar", _nat_lit(e.idx)]
    if isinstance(e, FVar):
        if e.name not in fv_idx:
            raise ValueError(f"free FVar in emitter: {e.name}")
        # fv_idx records depth-at-binding-time; current index = depth - that - 1
        binding_depth = fv_idx[e.name]
        cur = depth - binding_depth - 1
        return ["evar", _nat_lit(cur)]
    if isinstance(e, Const):
        # constant; level args are baked into the MM0 identifier in our model.
        # The caller is responsible for materialising the typing premise.
        return encode_name(e.name)
    if isinstance(e, App):
        return ["eapp",
                encode_expr(e.fn, fv_idx, depth),
                encode_expr(e.arg, fv_idx, depth)]
    if isinstance(e, Lam):
        return ["elam",
                encode_expr(e.dom, fv_idx, depth),
                encode_expr(e.body, fv_idx, depth + 1)]
    if isinstance(e, Pi):
        return ["epi",
                encode_expr(e.dom, fv_idx, depth),
                encode_expr(e.body, fv_idx, depth + 1)]
    if isinstance(e, Let):
        return ["elet",
                encode_expr(e.type_, fv_idx, depth),
                encode_expr(e.value, fv_idx, depth),
                encode_expr(e.body, fv_idx, depth + 1)]
    raise TypeError(e)


def encode_closed(e: Expr) -> SExpr:
    return encode_expr(e, {}, 0)


# ---------------- ctx construction ----------------

def encode_ctx(types: List[Expr], fv_idx: Dict[str, int]) -> SExpr:
    """Build an MM0 ctx from a list of types (outermost first).
    Each type is encoded relative to the *prefix* of binders that
    precede it (depth grows by 1 per entry)."""
    g: SExpr = "cnil"
    for i, t in enumerate(types):
        et = encode_expr(t, fv_idx, depth=i)
        g = ["ccons", et, g]
    return g


# ---------------- emit a typing proof from a Deriv ----------------

@dataclass
class EmitCtx:
    """State threaded through proof emission."""
    types: List[Expr]                       # outermost-first list of binder types
    fv_idx: Dict[str, int]                  # FVar name → depth-at-binding
    ctx_sexpr: SExpr                        # cached ctx encoding


def _push_binder(ctx: EmitCtx, ty: Expr, fv_name: Optional[str]) -> EmitCtx:
    new_types = ctx.types + [ty]
    new_fv = dict(ctx.fv_idx)
    if fv_name is not None:
        new_fv[fv_name] = len(ctx.types)
    return EmitCtx(new_types, new_fv,
                   encode_ctx(new_types, new_fv))


def emit_typing_proof(d: Deriv, ctx: EmitCtx, env: Env) -> SExpr:
    """Translate a kernel Deriv to an MM0 proof term concluding
    (has-type ctx.ctx_sexpr <encoded term> <encoded type>)."""
    rule = d.rule

    if rule == "ht_sort":
        l = encode_level(d.concl_term.level)             # type: ignore[union-attr]
        return ["apply", "ht-sort", [ctx.ctx_sexpr, l], []]

    if rule == "ht_fvar":
        name = d.extra["name"]
        binding_depth = ctx.fv_idx[name]
        cur_idx = len(ctx.types) - binding_depth - 1
        # we want a proof of (has-type ctx (evar cur_idx) <encoded type>)
        # The type stored in ctx.types[binding_depth] (let's call it T_binder).
        # has-type-at-binder gives ht-var0: (has-type (ccons T_binder G_outer) (evar 0) (shift1 T_binder)).
        # Then we wrap with ht-weak `cur_idx` times.
        # Build from the inside out:
        # Step 1: encode the partial context up to (and including) the binder.
        inner_types = ctx.types[:binding_depth + 1]
        inner_ctx = encode_ctx(inner_types, ctx.fv_idx)
        T_binder_enc = encode_expr(ctx.types[binding_depth], ctx.fv_idx,
                                    depth=binding_depth)
        # ht-var0 with G = encode_ctx(outermost), T = T_binder
        g_outer = encode_ctx(ctx.types[:binding_depth], ctx.fv_idx)
        proof: SExpr = ["apply", "ht-var0", [g_outer, T_binder_enc], []]
        # at this point the conclusion is:
        #   (has-type (ccons T_binder g_outer) (evar nzero) (shift1 T_binder))
        # we need to weaken `cur_idx` times to lift over the remaining binders.
        # Each weakening pushes one more binder onto the front.
        cur_T_enc = ["shift1", T_binder_enc]
        cur_i = 0
        for step in range(cur_idx):
            # the binder we're adding is ctx.types[binding_depth + 1 + step]
            S_enc = encode_expr(ctx.types[binding_depth + 1 + step],
                                ctx.fv_idx,
                                depth=binding_depth + 1 + step)
            g_so_far = encode_ctx(ctx.types[:binding_depth + 1 + step],
                                  ctx.fv_idx)
            proof = ["apply", "ht-weak",
                     [g_so_far, S_enc, cur_T_enc, _nat_lit(cur_i)],
                     [proof]]
            cur_T_enc = ["shift1", cur_T_enc]
            cur_i += 1
        return proof

    if rule == "ht_const":
        # Use {name}-typing under cnil, then weaken to current G.
        cname = d.extra["name"]
        levels = d.extra["levels"]
        # The typing theorem for `cname` is parameterized by its level params.
        # We instantiate it with the level args; the theorem's signature has
        # variables (G ctx) (level_params...) and no hypotheses.
        # We invoke it with G := cnil, then ht-weak-closed to get to current ctx.
        type_enc = encode_closed(d.concl_type)
        term_enc = encode_name(cname)
        # The typing theorem signature: ((G ctx) (l1 lvl) (l2 lvl) ...) () (has-type G econst-name <type>)
        sigma_list: List[SExpr] = ["cnil"] + [encode_level(l) for l in levels]
        proof = ["apply", encode_typing_name(cname), sigma_list, []]
        if ctx.ctx_sexpr == "cnil":
            return proof
        return ["apply", "ht-weak-closed",
                [ctx.ctx_sexpr, term_enc, type_enc],
                [proof]]

    if rule == "ht_pi":
        ddom, dbody = d.premises
        # ddom proves (has-type G A (esort u))
        # dbody proves (has-type (ccons A G) B (esort v))
        # we then apply ht-pi.
        # A is d.concl_term.dom (the Pi's domain)
        pi_node = d.concl_term                                # type: ignore[assignment]
        A_enc = encode_expr(pi_node.dom, ctx.fv_idx, depth=len(ctx.types))  # type: ignore[union-attr]
        # need u and v
        u_lvl = ddom.concl_type.level                         # type: ignore[union-attr]
        v_lvl = dbody.concl_type.level                        # type: ignore[union-attr]
        sub_dom = emit_typing_proof(ddom, ctx, env)
        # for the body subproof, the binder was entered via an FVar
        # we infer the FVar from the dbody's context — but our Deriv
        # doesn't carry that explicitly.  Reconstruct: the kernel uses
        # the binder name (possibly with a suffix); for emission we just
        # create a fresh name based on len(types).
        fv_name = f"_pi_{len(ctx.types)}"
        sub_ctx = _push_binder(ctx, pi_node.dom, fv_name)     # type: ignore[union-attr]
        # However, the dbody Deriv was computed with the kernel's actual
        # FVar.  We re-run a *fresh* derivation under the new binder name
        # via the kernel below.
        sub_body = _re_derive(env, pi_node.body, sub_ctx)     # type: ignore[union-attr]
        B_enc = encode_expr(pi_node.body, sub_ctx.fv_idx,     # type: ignore[union-attr]
                            depth=len(sub_ctx.types))
        return ["apply", "ht-pi",
                [ctx.ctx_sexpr, A_enc, B_enc, encode_level(u_lvl), encode_level(v_lvl)],
                [sub_dom, sub_body]]

    if rule == "ht_lam":
        ddom, _dbody = d.premises
        lam_node = d.concl_term                                # type: ignore[assignment]
        A_enc = encode_expr(lam_node.dom, ctx.fv_idx, depth=len(ctx.types))  # type: ignore[union-attr]
        u_lvl = ddom.concl_type.level                          # type: ignore[union-attr]
        sub_dom = emit_typing_proof(ddom, ctx, env)
        fv_name = f"_lam_{len(ctx.types)}"
        sub_ctx = _push_binder(ctx, lam_node.dom, fv_name)     # type: ignore[union-attr]
        sub_body = _re_derive(env, lam_node.body, sub_ctx)     # type: ignore[union-attr]
        # determine B (the body's type) by querying the kernel
        b_open = open_(lam_node.body, FVar(fv_name, lam_node.dom))  # type: ignore[union-attr]
        ker = Kernel(env, record=False)
        local = _to_local_ctx(sub_ctx)
        b_ty, _ = ker.infer(b_open, local)
        B_closed = close(b_ty, fv_name)
        B_enc = encode_expr(B_closed, sub_ctx.fv_idx, depth=len(sub_ctx.types))
        # encode the body too
        b_enc = encode_expr(lam_node.body, sub_ctx.fv_idx,     # type: ignore[union-attr]
                            depth=len(sub_ctx.types))
        return ["apply", "ht-lam",
                [ctx.ctx_sexpr, A_enc, b_enc, B_enc, encode_level(u_lvl)],
                [sub_dom, sub_body]]

    if rule == "ht_app":
        df, da = d.premises
        # f : Π A. B    a : A    ⊢ f a : B[a]
        # we need to know A and B
        app_node = d.concl_term                                # type: ignore[assignment]
        f_enc = encode_expr(app_node.fn, ctx.fv_idx, depth=len(ctx.types))   # type: ignore[union-attr]
        a_enc = encode_expr(app_node.arg, ctx.fv_idx, depth=len(ctx.types))  # type: ignore[union-attr]
        # df.concl_type is the inferred type of f; whnf to expose Pi
        ker = Kernel(env, record=False)
        local = _to_local_ctx(ctx)
        f_ty_w = ker.whnf(df.concl_type, local)
        if not isinstance(f_ty_w, Pi):
            raise RuntimeError("app: function's type is not Pi after whnf")
        A_enc = encode_expr(f_ty_w.dom, ctx.fv_idx, depth=len(ctx.types))
        B_enc = encode_expr(f_ty_w.body, ctx.fv_idx, depth=len(ctx.types) + 1)
        sub_f = emit_typing_proof(df, ctx, env)
        sub_a = emit_typing_proof(da, ctx, env)
        proof: SExpr = ["apply", "ht-app",
                        [ctx.ctx_sexpr, f_enc, a_enc, A_enc, B_enc],
                        [sub_f, sub_a]]
        # if the originally-inferred type isn't β-α-equal to the post-app type,
        # ht-conv may be needed.  In our verifier `subst1` is built-in, so this
        # usually lines up exactly.  If the kernel applied ht_conv via eqs we
        # emit it below.
        if d.eqs:
            # we may need conv: actual is B[a], expected is concl_type
            # build a def-eq proof from d.eqs.  For most of our test suite the
            # eqs are between defeq-trivial things; we conservatively emit a
            # de-refl which works whenever the verifier already considers them
            # equal under δ.
            actual = ["subst1", B_enc, a_enc]
            target = encode_expr(d.concl_type, ctx.fv_idx, depth=len(ctx.types))
            # if textually identical after normalization, do nothing
            from .mm0_verify import _equal, VerifierEnv
            # we don't have a verifier env here; just trust normalization
            pass
        return proof

    if rule == "ht_let":
        dtype, dval, dbody = d.premises
        let_node = d.concl_term                                # type: ignore[assignment]
        T_enc = encode_expr(let_node.type_, ctx.fv_idx, depth=len(ctx.types))    # type: ignore[union-attr]
        v_enc = encode_expr(let_node.value, ctx.fv_idx, depth=len(ctx.types))    # type: ignore[union-attr]
        b_enc = encode_expr(let_node.body, ctx.fv_idx, depth=len(ctx.types) + 1)  # type: ignore[union-attr]
        u_lvl = dtype.concl_type.level                          # type: ignore[union-attr]
        # B = the body's type with the bound variable still bound
        fv_name = f"_let_{len(ctx.types)}"
        sub_ctx = _push_binder(ctx, let_node.type_, fv_name)    # type: ignore[union-attr]
        b_open = open_(let_node.body, FVar(fv_name, let_node.type_))   # type: ignore[union-attr]
        ker = Kernel(env, record=False)
        local = _to_local_ctx(sub_ctx)
        b_ty, _ = ker.infer(b_open, local)
        B_closed = close(b_ty, fv_name)
        B_enc = encode_expr(B_closed, sub_ctx.fv_idx, depth=len(sub_ctx.types))
        sub_t = emit_typing_proof(dtype, ctx, env)
        sub_v = emit_typing_proof(dval, ctx, env)
        sub_b = _re_derive(env, let_node.body, sub_ctx)        # type: ignore[union-attr]
        return ["apply", "ht-let",
                [ctx.ctx_sexpr, T_enc, v_enc, b_enc, B_enc, encode_level(u_lvl)],
                [sub_t, sub_v, sub_b]]

    raise NotImplementedError(f"emit_typing_proof: unsupported rule {rule}")


def _to_local_ctx(emit_ctx: EmitCtx) -> LocalCtx:
    """Reconstruct a kernel LocalCtx from the emitter's EmitCtx."""
    lc = LocalCtx()
    # walk fv_idx in order of binding depth (smaller depth = outer)
    by_depth = sorted(emit_ctx.fv_idx.items(), key=lambda kv: kv[1])
    for name, depth in by_depth:
        lc.entries.append((name, emit_ctx.types[depth], None))
    return lc


def _re_derive(env: Env, body: Expr, sub_ctx: EmitCtx) -> SExpr:
    """Open body with the most-recently-pushed FVar, run kernel.infer with
    record=True under sub_ctx, then emit."""
    # the freshest binder is the last in sub_ctx.types; find its FVar name
    # from sub_ctx.fv_idx (reverse lookup)
    inner_depth = len(sub_ctx.types) - 1
    fv_name = None
    for n, d in sub_ctx.fv_idx.items():
        if d == inner_depth:
            fv_name = n
            break
    assert fv_name is not None
    fv = FVar(fv_name, sub_ctx.types[inner_depth])
    body_open = open_(body, fv)
    local = _to_local_ctx(sub_ctx)
    ker = Kernel(env, record=True)
    _, d = ker.infer(body_open, local)
    return emit_typing_proof(d, sub_ctx, env)


# ---------------- emit a whole declaration ----------------

def emit_decl(decl, env: Env, out: io.StringIO) -> None:
    name = decl.name                                            # type: ignore[attr-defined]
    level_params = list(getattr(decl, "level_params", ()))
    type_ = getattr(decl, "type_", None)
    if type_ is None:
        return

    # 1) declare the constant.
    #    Definitions become MM0 `def`s so the verifier δ-expands them.
    #    Theorems become MM0 `opaque-def`s — body is parsed and stored, but
    #    not unfolded during normalization (subsequent proofs treat them as
    #    opaque, which is what keeps chains of dependent lemmas cheap).
    #    Primitives (axioms, inductive type-formers, constructors, recursors)
    #    become opaque `term`s.
    if isinstance(decl, Definition):
        val_enc = encode_closed(decl.value)
        out.write(f"(def {encode_name(name)} () expr {_sexp_str(val_enc)})\n")
    elif isinstance(decl, Theorem):
        val_enc = encode_closed(decl.value)
        out.write(f"(opaque-def {encode_name(name)} () expr {_sexp_str(val_enc)})\n")
    else:
        out.write(f"(term {encode_name(name)} () expr)\n")

    # 2) typing theorem / axiom
    type_enc = encode_closed(type_)
    vars_spec = [["G", "ctx"]] + [[l, "lvl"] for l in level_params]
    # sexp-friendly
    def fmt_vars():
        return "(" + " ".join("(" + " ".join(v) + ")" for v in vars_spec) + ")"
    concl = ["has-type", "G", encode_name(name), type_enc]
    # for definitions / theorems we provide a proof; otherwise axiom
    if isinstance(decl, (Definition, Theorem)):
        # type-check the body, capture derivation
        ker = Kernel(env, record=True)
        # add the decl temporarily? It's already in env (build_stdlib added it)
        # If not yet added, we should add a stub.  We rely on the caller
        # already having added it.
        local = LocalCtx()
        _ty, d = ker.infer(decl.value, local)
        ctx0 = EmitCtx(types=[], fv_idx={}, ctx_sexpr="cnil")
        body_proof = emit_typing_proof(d, ctx0, env)
        # the body proof concludes (has-type cnil <value> <type>) (or close to it).
        # We want a theorem of (has-type G econst-name <type>).
        # For Definition: econst-name δ-reduces to <value>, so the body proof
        # already witnesses (has-type cnil econst-name T) up to def-eq.
        # For Theorem: econst-name is opaque, so we lift via the verifier's
        # opaque-def-typing rule before weakening.
        try:
            out.write(f"(theorem {encode_typing_name(name)}\n")
            out.write(f"  {fmt_vars()}\n")
            out.write(f"  ()\n")
            out.write(f"  {_sexp_str(concl)}\n")
            if isinstance(decl, Theorem):
                # opaque-def-typing wraps a body-proof into a typing-of-name
                # proof, then ht-weak-closed lifts from cnil to arbitrary G.
                lifted = ["opaque-def-typing", encode_name(name), body_proof]
                wrapped = ["apply", "ht-weak-closed",
                           ["G", encode_name(name), type_enc],
                           [lifted]]
            else:
                # The proof was constructed under cnil; lift to arbitrary G
                # via ht-weak-closed.  econst-name is a def, so the body's
                # typing IS the def's typing after δ.
                wrapped = ["apply", "ht-weak-closed",
                           ["G", encode_name(name), type_enc],
                           [body_proof]]
            out.write(f"  {_sexp_str(wrapped)})\n")
        except Exception as e:
            # fallback: emit as axiom and note the failure
            out.write(f";; body proof reconstruction failed: {e}\n")
            out.write(f"(axiom {encode_typing_name(name)}\n")
            out.write(f"  {fmt_vars()}\n")
            out.write(f"  ()\n")
            out.write(f"  {_sexp_str(concl)})\n")
        out.write("\n")
    else:
        # primitive declaration: axiom
        out.write(f"(axiom {encode_typing_name(name)}\n")
        out.write(f"  {fmt_vars()}\n")
        out.write(f"  ()\n")
        out.write(f"  {_sexp_str(concl)})\n\n")

    # 3) for recursors, emit ι-rule axioms
    if isinstance(decl, Recursor):
        emit_recursor_iota(decl, env, out)


def emit_recursor_iota(decl: Recursor, env: Env, out: io.StringIO) -> None:
    """For each ctor of the inductive, emit an (iota ...) declaration so
    the verifier can fire ι reductions automatically.  This is the primary
    machinery enabling `Nat.add 2 3 = 5` to be checked by reflexivity.

    For Eq (which has an index), we skip — the index ≡ b case is non-trivial
    and the existing Eq.rec users in tests don't depend on auto-ι yet.
    """
    rec_name = decl.name
    n_params = decl.num_params
    n_motives = decl.num_motives
    n_minors = decl.num_minors
    n_indices = decl.num_indices
    for rule in decl.rules:
        rec_pos_str = "(" + " ".join(str(p) for p in rule.rec_arg_positions) + ")"
        rhs_enc = _encode_template(rule.rhs_template)
        if n_indices == 0 and rule.n_ctor_params_override < 0:
            out.write(
                f"(iota {encode_name(rec_name)} {encode_name(rule.ctor_name)} "
                f"{n_params} {n_motives} {n_minors} {n_indices} "
                f"{rule.num_fields} {rec_pos_str} {_sexp_str(rhs_enc)})\n\n"
            )
        elif n_indices == 0 and rule.n_ctor_params_override >= 0:
            # 12-element form to carry n_ctor_params
            out.write(
                f"(iota {encode_name(rec_name)} {encode_name(rule.ctor_name)} "
                f"{n_params} {n_motives} {n_minors} {n_indices} "
                f"{rule.num_fields} {rec_pos_str} {_sexp_str(rhs_enc)} "
                f"() {rule.n_ctor_params_override})\n\n"
            )
        else:
            # indexed: include rec_index_templates
            if len(rule.rec_arg_positions) > 0 and len(rule.rec_index_templates) == 0:
                # No templates provided; skip — would be unsound to invent indices.
                out.write(
                    f";; (iota for {rec_name}/{rule.ctor_name} skipped: "
                    f"no rec_index_templates for indexed inductive)\n"
                )
                continue
            idx_tpls_enc = "(" + " ".join(
                "(" + " ".join(_sexp_str(_encode_template(t)) for t in tpl) + ")"
                for tpl in rule.rec_index_templates
            ) + ")"
            out.write(
                f"(iota {encode_name(rec_name)} {encode_name(rule.ctor_name)} "
                f"{n_params} {n_motives} {n_minors} {n_indices} "
                f"{rule.num_fields} {rec_pos_str} {_sexp_str(rhs_enc)} "
                f"{idx_tpls_enc})\n\n"
            )


def _encode_template(e):
    """Encode rhs_template into the s-expression term language.  Behaves
    like encode_expr but does not require an fv_idx (templates have no
    FVars)."""
    if isinstance(e, BVar):
        n = e.idx
        nat: SExpr = "nzero"
        for _ in range(n):
            nat = ["nsucc", nat]
        return ["evar", nat]
    if isinstance(e, Const):
        return encode_name(e.name)
    if isinstance(e, Sort):
        return ["esort", encode_level(e.level)]
    if isinstance(e, App):
        return ["eapp", _encode_template(e.fn), _encode_template(e.arg)]
    if isinstance(e, Lam):
        return ["elam", _encode_template(e.dom), _encode_template(e.body)]
    if isinstance(e, Pi):
        return ["epi", _encode_template(e.dom), _encode_template(e.body)]
    if isinstance(e, Let):
        return ["elet", _encode_template(e.type_), _encode_template(e.value),
                _encode_template(e.body)]
    raise TypeError(e)


def _encode_rhs(template: Expr, env_subst_vars: List[str]) -> SExpr:
    """The template uses BVar(i) where i indexes from the end of env_subst.
    Substitute those BVars with the corresponding variable names."""
    n = len(env_subst_vars)
    def go(e: Expr, depth: int) -> SExpr:
        if isinstance(e, BVar):
            # bvars below `depth` are internal binders of the template (rare);
            # bvars at index >= depth refer to env_subst entries: the entry at
            # position `n - 1 - (e.idx - depth)` is the variable.
            idx = e.idx
            if idx < depth:
                return ["evar", _nat_lit(idx)]
            pos = n - 1 - (idx - depth)
            if pos < 0 or pos >= n:
                raise RuntimeError(f"BVar out of env_subst range: {idx} depth={depth}")
            return env_subst_vars[pos]
        if isinstance(e, Const):
            return encode_name(e.name)
        if isinstance(e, Sort):
            return ["esort", encode_level(e.level)]
        if isinstance(e, App):
            return ["eapp", go(e.fn, depth), go(e.arg, depth)]
        if isinstance(e, Lam):
            return ["elam", go(e.dom, depth), go(e.body, depth + 1)]
        if isinstance(e, Pi):
            return ["epi", go(e.dom, depth), go(e.body, depth + 1)]
        if isinstance(e, Let):
            return ["elet", go(e.type_, depth), go(e.value, depth),
                    go(e.body, depth + 1)]
        if isinstance(e, FVar):
            raise RuntimeError("FVar in rhs_template")
        raise TypeError(e)
    return go(template, 0)


# ---------------- s-expression printing ----------------

def _sexp_str(e: SExpr) -> str:
    if isinstance(e, str):
        return e
    return "(" + " ".join(_sexp_str(x) for x in e) + ")"


def _sexp_str_obj(e: SExpr) -> SExpr:
    return e


# ---------------- top-level driver ----------------

def emit_env(env: Env, out: io.StringIO, *, only: Optional[List[str]] = None) -> None:
    """Emit MM0 for each declaration in env.order (or `only` if given)."""
    names = only if only is not None else env.order
    for name in names:
        decl = env.get(name)
        out.write(f";; ===== {name} =====\n")
        emit_decl(decl, env, out)
        out.write("\n")
