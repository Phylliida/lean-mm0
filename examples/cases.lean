-- `cases` tactic (v1): case-splits on a non-recursive non-indexed
-- inductive scrutinee, producing one subgoal per ctor.  Each subgoal
-- has type `Π fields..., goal`; the user introduces the fields with
-- intro and then provides a term.

-- The simplest case: split on a Bool.  Two subgoals, each with no
-- fields, both solved by Eq.refl.
def use_bool (b : Bool) : Nat :=
  by cases b; exact 0; exact 1

-- Bool's ctor order in the prelude is (false, true), so the first
-- subgoal is the false case.
example : Eq.{1} Nat (use_bool Bool.false) 0 := by rfl
example : Eq.{1} Nat (use_bool Bool.true) 1 := by rfl

-- Or with a Decidable: 2 subgoals, each takes one field (the proof).
def decide_demo (d : Decidable True) : Nat :=
  by cases d; intro h; exact 0; intro h; exact 1

example : Eq.{1} Nat (decide_demo instDecidableTrue) 1 := by rfl

-- Cases on Sum.{1, 1} Nat Bool: one subgoal per ctor (Sum.inl, Sum.inr).
def sum_to_nat (x : Sum.{1, 1} Nat Bool) : Nat :=
  by cases x; intro a; exact a; intro b; exact 7

example : Eq.{1} Nat (sum_to_nat (Sum.inl.{1, 1} Nat Bool 42)) 42 := by rfl
example : Eq.{1} Nat (sum_to_nat (Sum.inr.{1, 1} Nat Bool Bool.true)) 7 := by rfl

-- Cases on Nat: 2 subgoals.  Zero takes no fields.  Succ takes a Nat
-- field and an IH (ignored here — cases doesn't expose recursion as
-- naturally as a real `induction` tactic would).
def is_zero_nat (n : Nat) : Bool :=
  by cases n; exact Bool.true; intro k; intro ih; exact Bool.false

example : Eq.{1} Bool (is_zero_nat 0) Bool.true := by rfl
example : Eq.{1} Bool (is_zero_nat 5) Bool.false := by rfl
