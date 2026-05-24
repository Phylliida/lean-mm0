-- Decidable + if/then/else.
--
-- `Decidable p` is a Type-valued inductive with two constructors:
--   isFalse : Not p → Decidable p
--   isTrue  : p → Decidable p
--
-- `if c then t else e` desugars to `@ite _ c _ t e`; the elaborator
-- fills the type and the Decidable instance via inst-synthesis.

-- Underscores as holes (the elaborator generates fresh metas).
example : Eq.{1} Nat (@ite.{1} Nat True instDecidableTrue 5 7) 5 :=
  Eq.refl.{1} Nat 5

-- Same thing with sugar.
example : Eq.{1} Nat (if True then 5 else 7) 5 := by rfl
example : Eq.{1} Nat (if False then 5 else 7) 7 := by rfl

-- ite reduces via Decidable.rec's iota rule.
def choose (c : Prop) (d : Decidable c) (n : Nat) : Nat :=
  if c then n else 0

-- Eta-expanding so the inst-implicit gets discharged explicitly here.
example : Eq.{1} Nat (choose True instDecidableTrue 42) 42 := by rfl
example : Eq.{1} Nat (choose False instDecidableFalse 42) 0 := by rfl

-- Nested.
example : Eq.{1} Nat
    (if True then (if False then 1 else 2) else 3) 2 := by rfl
