-- Higher-order pattern unification demo.
--
-- Eq.subst's signature has an implicit motive `p : α → Sort v`.
-- The elaborator infers it by solving `?p x = T` for some `?p`.
-- Without HOP, this fails (?p applied to x doesn't match T directly).
-- With HOP, the elaborator abstracts `x` out of `T` to build the motive.

axiom Eq.substI.{u, v} :
  {a : Sort u} -> {p : a -> Sort v} -> {x : a} -> {y : a} ->
  Eq.{u} a x y -> p x -> p y

-- Case B (constant motive): args are literals, but the rhs doesn't
-- depend on them — HOP produces `?p := λ _. Eq Nat 7 7`.
def use_subst_b : Eq.{1} Nat 7 7 :=
  Eq.substI.{1, 0}
    (Eq.refl.{1} Nat 7)
    (Eq.refl.{1} Nat 7)

-- Case A (Miller pattern): args are FVars in the local context.
-- HOP abstracts `x` out of `Eq a x x` to give motive `λ x. Eq a x x`.
def rewrite_refl.{u}
    {a : Sort u} (x y : a) (h : Eq.{u} a x y) (refl_x : Eq.{u} a x x)
    : Eq.{u} a y y :=
  Eq.substI.{u, 0} h refl_x

-- Use it concretely
def example : Eq.{1} Nat 7 7 :=
  rewrite_refl.{1} 7 7 (Eq.refl.{1} Nat 7) (Eq.refl.{1} Nat 7)
