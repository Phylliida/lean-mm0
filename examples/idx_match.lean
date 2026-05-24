-- Match on indexed inductives (v1: requires (motive := ...) and no
-- recursive constructors).  Eq is the canonical example.

-- A roundabout proof that Eq is symmetric, by matching on the proof.
def my_eq_symm.{u} {α : Sort u} (a b : α) (h : Eq.{u} α a b) : Eq.{u} α b a :=
  match (motive := fun (b2 : α) (_ : Eq.{u} α a b2) => Eq.{u} α b2 a) h with
  | Eq.refl => Eq.refl.{u} α a

-- And similarly: matching is the same as Eq.rec, here used to transport
-- a property along an equality.
def transport.{u, v} {α : Sort u}
    (P : α -> Sort v) {a b : α} (h : Eq.{u} α a b) (p : P a) : P b :=
  match (motive := fun (b2 : α) (_ : Eq.{u} α a b2) => P b2) h with
  | Eq.refl => p

-- Sanity: my_eq_symm on a refl reduces.
example : Eq.{0} (Eq.{1} Nat 3 3) (my_eq_symm 3 3 (Eq.refl.{1} Nat 3))
                                  (Eq.refl.{1} Nat 3) := by rfl
