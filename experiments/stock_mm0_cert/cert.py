"""Prototype: a CERTIFYING emitter for CIC -> stock MM0.

UNTRUSTED.  Takes CIC terms and emits *explicit* stock-MM0 proofs (against
Mario Carneiro's lean.mm1 prelude) of facts our own verifier discharges
with a single `de-refl` (because it computes beta/iota/zeta in the trusted
base).  A stock MM0 verifier (mm0-rs / mm0-c) then checks the emitted proof
with NO computation in its trusted core.

This is the feasibility prototype for "drop our beta/iota/zeta evaluator
from the trusted base and certify every reduction instead".

Layers:
  * Layer 1 -- substitution certificates: prove_subst(A, e, x) emits a proof
    of `subst: A[e/x] = B`.  Self-contained (subst_* axioms need no typing).
  * Layer 2 -- beta certificates (see cert_beta.py): conv_beta + Layer-1
    substitution proofs + congruence, chained with conv_trans.

KEY DEMONSTRATION: with a fresh-name supply for binders, the disjoint-
variable / alpha-renaming bookkeeping that made hand-authoring painful
(experiment #1) becomes automatic -- every binder is globally unique, so
subst_lambda / congruence never hit a variable capture.
"""
from __future__ import annotations
from dataclasses import dataclass
import re

# ----------------------------------------------------------------------
# CIC term AST, in lean.mm1's named-binder syntax
# ----------------------------------------------------------------------
class Term: pass

@dataclass(frozen=True)
class Sort(Term):
    lvl: str                 # "L0", "L1", "(l_S u)", ...

@dataclass(frozen=True)
class Var(Term):
    name: str

@dataclass(frozen=True)
class Const(Term):
    name: str                # nat, nat_zero, nat_succ, ...

@dataclass(frozen=True)
class App(Term):
    fn: Term
    arg: Term

@dataclass(frozen=True)
class Lam(Term):
    var: str
    ty: Term
    body: Term

@dataclass(frozen=True)
class Pi(Term):
    var: str
    ty: Term
    body: Term

@dataclass(frozen=True)
class Imp(Term):                     # non-dependent function type  A -> B
    dom: Term
    cod: Term

@dataclass(frozen=True)
class NatRec(Term):                  # the recursor  nat_rec u  (u a level)
    lvl: str


def pp(t: Term) -> str:
    """Pretty-print to lean.mm1 surface syntax."""
    if isinstance(t, Sort):   return f"Sort {t.lvl}"
    if isinstance(t, Var):    return t.name
    if isinstance(t, Const):  return t.name
    if isinstance(t, App):    return f"({pp(t.fn)} @ {pp(t.arg)})"
    if isinstance(t, Lam):    return f"(\\. {t.var} : {pp(t.ty)}, {pp(t.body)})"
    if isinstance(t, Pi):     return f"(A. {t.var} : {pp(t.ty)}, {pp(t.body)})"
    if isinstance(t, Imp):    return f"({pp(t.dom)} -> {pp(t.cod)})"
    if isinstance(t, NatRec): return f"(nat_rec {t.lvl})"
    raise TypeError(t)


def fv(t: Term) -> set:
    """Free (named) variables."""
    if isinstance(t, (Sort, Const, NatRec)): return set()
    if isinstance(t, Var):                   return {t.name}
    if isinstance(t, App):                   return fv(t.fn) | fv(t.arg)
    if isinstance(t, (Lam, Pi)):             return fv(t.ty) | (fv(t.body) - {t.var})
    if isinstance(t, Imp):                   return fv(t.dom) | fv(t.cod)
    raise TypeError(t)


# ----------------------------------------------------------------------
# Fresh-name supply -- the thing that makes alpha-management automatic
# ----------------------------------------------------------------------
class Fresh:
    def __init__(self, prefix="v"):
        self.n = 0
        self.prefix = prefix
    def __call__(self) -> str:
        s = f"{self.prefix}{self.n}"
        self.n += 1
        return s


# ----------------------------------------------------------------------
# Layer 1: substitution certificates
#   prove_subst(A, e, x) -> (B, proof) with B = A[e/x] and
#   `proof` a lean.mm1 proof term of   subst: A [e/x] = B
# ----------------------------------------------------------------------
def prove_subst(A: Term, e: Term, x: str):
    # x not free  ->  one node, the whole subterm is unchanged
    if x not in fv(A):
        return A, "subst_nf"
    if isinstance(A, Var):                       # A == Var(x) since x in fv
        return e, "subst_var"
    if isinstance(A, App):
        f2, pf = prove_subst(A.fn,  e, x)
        a2, pa = prove_subst(A.arg, e, x)
        return App(f2, a2), f"(subst_app {pf} {pa})"
    if isinstance(A, Imp):
        d2, pd = prove_subst(A.dom, e, x)
        c2, pc = prove_subst(A.cod, e, x)
        return Imp(d2, c2), f"(subst_imp {pd} {pc})"
    if isinstance(A, (Lam, Pi)):
        # binder is globally fresh -> binder != x and binder not in fv(e),
        # so subst_{lambda,Pi} applies with no capture and no alpha-renaming
        if A.var == x or A.var in fv(e):
            raise AssertionError(
                f"binder {A.var!r} not fresh wrt subst [{pp(e)}/{x}] "
                f"-- the emitter must alpha-rename first")
        t2, pt = prove_subst(A.ty,   e, x)
        b2, pb = prove_subst(A.body, e, x)
        ctor = Lam if isinstance(A, Lam) else Pi
        ax   = "subst_lambda" if isinstance(A, Lam) else "subst_Pi"
        return ctor(A.var, t2, b2), f"({ax} {pt} {pb})"
    raise TypeError(A)


# ----------------------------------------------------------------------
# emit a self-contained `theorem` + proof-node accounting
# ----------------------------------------------------------------------
_AX = re.compile(r'[A-Za-z_]\w*')
_SUBST_AXIOMS = {"subst_nf", "subst_var", "subst_app", "subst_lambda",
                 "subst_Pi", "subst_imp", "subst_lambda_1", "subst_Pi_1"}

def proof_nodes(proof: str) -> int:
    return sum(1 for tok in _AX.findall(proof) if tok in _SUBST_AXIOMS)

def emit_subst_theorem(name: str, A: Term, e: Term, x: str) -> tuple[str, int]:
    B, proof = prove_subst(A, e, x)
    stmt = f"subst: {pp(A)} [ {pp(e)} / {x} ] = {pp(B)}"
    thm = f"theorem {name}: $ {stmt} $ =\n'{proof};\n"
    return thm, proof_nodes(proof)
