-- intro is now a standalone tactic that the seq interpreter handles
-- specially: leading intros push their FVars onto the local ctx (peeling
-- Π binders off the goal), and subsequent tactics — including ones that
-- solve subgoals produced by `apply` — see those FVars.
--
-- Concretely: `intro h; apply f h; rfl; rfl` works even though the
-- rfl's solve subgoals f produces.  Under the older nested intro, the
-- subgoals had no consumer outside intro's body.

-- The classic, no intros.
example : Eq.{1} Nat 3 3 :=
  by apply @Eq.trans.{1} Nat 3 3 3; rfl; rfl

-- intro then apply with multiple subgoals; both subgoals solved by
-- rfls AFTER the intro, in the intro'd ctx.
def transit : Nat -> Eq.{1} Nat 3 3 :=
  by intro k; apply @Eq.trans.{1} Nat 3 3 3; rfl; rfl

-- Two intros, then apply, then rfls.
def transit2 : Nat -> Nat -> Eq.{1} Nat 3 3 :=
  by intro k; intro l; apply @Eq.trans.{1} Nat 3 3 3; rfl; rfl

-- intro followed by a complex apply that uses both the introduced
-- hypothesis and trailing tactics for sub-proofs.
def from_eq_seq.{u} {T : Sort u} (x y : T) : Eq.{u} T x y -> Eq.{u} T y x :=
  by intro h; apply Eq.symm; assumption

-- A subgoal that doesn't reference the introduced var — still solved
-- in the same seq.
def add_self : Nat -> Eq.{1} Nat 4 4 :=
  by intro k; apply Eq.refl

