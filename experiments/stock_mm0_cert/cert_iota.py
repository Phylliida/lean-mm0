"""Layer 3: iota (recursor) certificates -- the certifying evaluator's core.

`norm_rec` certifies a nat recursor computation by citing the pre-proven
schematic iota rules (`nat_succ_iota`, `nat_zero_iota`) and chaining them
with congruence + `conv_trans`.  It returns

    (nf, conv, nf_typing)

where  conv       proves   G |= nat_rec u @ C @ z @ s @ major = nf
       nf_typing  proves   G |- nf : C @ major

The trick that keeps this cheap: we never re-type the recursor application
itself.  Each step threads the *result's* typing (`nf_typing`) and uses
`conv_ty_r` to build the typed conversion for the congruence -- exactly the
shape of the hand-written `ground_two_steps` from experiment #1, but
generated for arbitrary recursion depth.

This module handles abstract motive/z/s (passed as hypotheses).  Concrete
ground computation (`run_iota_concrete`) instantiates them and generates the
motive-typing bridges automatically.
"""
from __future__ import annotations
from cert import (Var, Const, App, Lam, Pi, Imp, NatRec, pp, fv, prove_subst)
from cert_beta import prove_type, conv_trans

ZERO = Const("nat_zero")
SUCC = Const("nat_succ")

def numeral(m: int):
    t = ZERO
    for _ in range(m):
        t = App(SUCC, t)
    return t


def norm_rec(u, C, z, s, major, hyps, ctx, env):
    """Certify  nat_rec u @ C @ z @ s @ major = nf  for a literal `major`.

    hyps = (hC, hz, hs): proof terms for
        hC : C : nat -> Sort u
        hz : z : C @ nat_zero
        hs : s : A n:nat, C@n -> C@(succ n)
    Returns (nf, conv, nf_typing)."""
    hC, hz, hs = hyps
    if isinstance(major, Const) and major.name == "nat_zero":
        # base: rec ... nat_zero = z
        return z, f"(nat_zero_iota {hC} {hz} {hs})", hz
    if isinstance(major, App) and major.fn == SUCC:
        k = major.arg
        # iota:  rec ... (succ k) = s @ k @ (rec ... k)
        iota = f"(nat_succ_iota {hC} {hz} {hs})"
        # recursively normalise the inner  rec ... k
        reck_nf, reck_conv, reck_ty = norm_rec(u, C, z, s, k, hyps, ctx, env)
        # type of  s @ k : C@k -> C@(succ k)
        _skt, sk_proof = prove_type(App(s, k), ctx, env)
        nf = App(App(s, k), reck_nf)
        nf_ty = f"(ty_ndapp {sk_proof} {reck_ty})"          # nf : C@(succ k)
        # congruence:  s @ k @ (rec..k)  =  s @ k @ reck_nf
        reck_typed = f"(conv_ty_r {reck_ty} {reck_conv})"   # |=: rec..k = reck_nf : C@k
        cong = (f"(and_right (conv_ty_ndapp (conv_ty_refl {sk_proof}) "
                f"{reck_typed}))")
        return nf, f"(conv_trans {iota} {cong})", nf_ty
    raise ValueError(f"major is not a literal numeral: {pp(major)}")
