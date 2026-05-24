-- A tiny Lean-ish source file consumed by the lean-mm0 backend.
-- The parser accepts a strict subset of Lean 4 syntax with NO implicit
-- arguments, NO type-class instances, and NO tactic blocks — everything
-- must be fully explicit.  This is enough to exercise the pipeline
-- end-to-end on real text input.

-- Universe-polymorphic identity
def id_poly.{u} (a : Sort u) (x : a) : a := x

-- Two-universe const combinator
def const_fn.{u, v} (a : Sort u) (b : Sort v) (x : a) (y : b) : a := x

-- Computation on Nat through a `def`
def double (n : Nat) : Nat := Nat.add n n

def six : Nat := double 3

def succ_fun : (n : Nat) -> Nat := fun (n : Nat) => Nat.succ n

-- Polymorphic let-binding
def let_id : Nat := let x : Nat := 5; succ_fun x

-- Propositional theorems verified by definitional equality (β/δ/ι/ζ)
theorem id_Nat_42_eq : Eq.{1} Nat (id_poly.{1} Nat 42) 42 :=
  Eq.refl.{1} Nat 42

theorem double_3_eq_6 : Eq.{1} Nat six 6 :=
  Eq.refl.{1} Nat 6

theorem let_eval : Eq.{1} Nat let_id 6 :=
  Eq.refl.{1} Nat 6

-- Function composition (manually instantiated, no implicits)
def compose_NNN (g : (n : Nat) -> Nat) (f : (n : Nat) -> Nat) (x : Nat) : Nat :=
  g (f x)

def add_two : Nat -> Nat := fun (n : Nat) => Nat.add n 2

theorem comp_eval : Eq.{1} Nat (compose_NNN add_two add_two 10) 14 :=
  Eq.refl.{1} Nat 14
