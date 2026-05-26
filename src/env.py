"""Environment of CIC declarations.

A declaration is one of:
  Definition  name, level_params, type, value
  Axiom       name, level_params, type
  Inductive   name, level_params, type, constructors, recursor
  Constructor name, level_params, type, inductive_name, index
  Recursor    name, level_params, type, inductive_name, rules
"""
from __future__ import annotations
from dataclasses import dataclass, field
from typing import Tuple, Dict, Optional, List
from .expr import Expr


@dataclass(frozen=True)
class Definition:
    name: str
    level_params: Tuple[str, ...]
    type_: Expr
    value: Expr


@dataclass(frozen=True)
class Theorem:
    """A proven proposition.  Structurally identical to Definition (we keep
    the body so the kernel/elaborator can type-check it), but the kernel
    treats it as opaque: `whnf` does not δ-unfold it.  The emitter emits it
    as an MM0 `opaque-def`, so the verifier does not unfold it either,
    keeping subsequent proofs' verification cheap."""
    name: str
    level_params: Tuple[str, ...]
    type_: Expr
    value: Expr


@dataclass(frozen=True)
class Axiom:
    name: str
    level_params: Tuple[str, ...]
    type_: Expr


@dataclass(frozen=True)
class Constructor:
    name: str
    level_params: Tuple[str, ...]
    type_: Expr
    inductive: str
    index: int               # 0-based position among the inductive's constructors
    num_params: int          # how many of the leading binders are inductive params
    num_fields: int          # remaining argument count


@dataclass(frozen=True)
class RecursorRule:
    """One ι-reduction rule:
        rec params motives minors indices (ctor params fields)
                                              ⟶  minor_i applied to fields
                                                  (with recursive calls)
    """
    ctor_name: str
    num_fields: int
    num_rec_args: int                            # recursive positions among the fields
    rhs_template: Expr                           # open RHS over env_subst
    rec_arg_positions: Tuple[int, ...]
    # For indexed inductives only: per recursive arg, a tuple of n_indices
    # index expressions (in the env_subst-without-rec_results convention)
    rec_index_templates: Tuple[Tuple[Expr, ...], ...] = ()
    # When the ctor has fewer params than the recursor (Quot.lift / Quot.mk).
    n_ctor_params_override: int = -1                 # -1 = use Recursor.num_params


@dataclass(frozen=True)
class Recursor:
    name: str
    level_params: Tuple[str, ...]
    type_: Expr
    inductive: str
    num_params: int
    num_motives: int
    num_minors: int
    num_indices: int
    motive_universe_param: Optional[str]    # the level param the motive lives at
    rules: Tuple[RecursorRule, ...]


@dataclass(frozen=True)
class Inductive:
    name: str
    level_params: Tuple[str, ...]
    type_: Expr
    num_params: int
    num_indices: int
    constructor_names: Tuple[str, ...]
    recursor_name: str


Decl = "Definition | Theorem | Axiom | Constructor | Recursor | Inductive"


class Env:
    def __init__(self) -> None:
        self.decls: Dict[str, object] = {}
        self.order: List[str] = []
        # class_head_name -> list of instance Definition names
        self.instances: Dict[str, List[str]] = {}
        # @[simp] lemmas: names of theorems / defs whose conclusion is
        # `Eq α a b` and that should be auto-included by the simp tactic.
        self.simp_lemmas: List[str] = []

    def add(self, decl) -> None:
        name = decl.name           # type: ignore[attr-defined]
        if name in self.decls:
            raise KeyError(f"duplicate declaration {name!r}")
        self.decls[name] = decl
        self.order.append(name)

    def get(self, name: str):
        if name not in self.decls:
            raise KeyError(f"unknown declaration {name!r}")
        return self.decls[name]

    def has(self, name: str) -> bool:
        return name in self.decls

    def register_instance(self, inst_name: str, class_head: str) -> None:
        """Record that `inst_name` is an instance of class `class_head`."""
        self.instances.setdefault(class_head, []).append(inst_name)

    def instances_of(self, class_head: str) -> List[str]:
        return self.instances.get(class_head, [])

    def register_simp_lemma(self, name: str) -> None:
        """Add a lemma to the global `simp` set."""
        if name not in self.simp_lemmas:
            self.simp_lemmas.append(name)
