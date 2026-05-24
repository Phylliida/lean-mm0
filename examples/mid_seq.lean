-- Mid-sequence intros: `intro` is allowed at any position in the tactic
-- seq.  When focus has shifted to a subgoal (e.g. via `apply`), an intro
-- peels the focused subgoal's Π.  The subgoal-solving terms can use
-- both the original main-goal intros and any subgoal-local intros.

-- A higher-order helper: takes any function on Nat and applies it to 7.
def call_at_seven.{u} {α : Sort u} (f : Nat -> α) : α := f 7

-- Apply yields a subgoal `Nat -> Nat`; intro k peels it, exact k solves.
example : Nat := by apply @call_at_seven.{1} Nat; intro k; exact k
example : Eq.{1} Nat (call_at_seven.{1} (fun (k : Nat) => k)) 7 := by rfl

-- Mid-seq intro that uses both an outer intro and a subgoal-local one.
def use_both.{u} {α : Sort u} (a : α) (f : Nat -> α) : α := f 7

-- Goal Nat: introduce a Nat from the main goal, then apply use_both with
-- that Nat as the first arg; the remaining subgoal `Nat -> Nat` is
-- intro'd and solved by returning the main-intro'd value.
def constish : Nat -> Nat := by
  intro m;
  apply @use_both.{1} Nat m;
  intro k;
  exact m

example : Eq.{1} Nat (constish 42) 42 := by rfl

-- A subgoal that itself produces subgoals via another apply.
def deeper.{u} {α : Sort u} (f : Nat -> Nat -> α) : α := f 1 2

example : Nat := by
  apply @deeper.{1} Nat;
  intro a;
  intro b;
  exact b
