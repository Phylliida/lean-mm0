-- Demonstrate Lean-style `{x : T}` IMPLICIT binders.
-- The elaborator inserts metavariables for {α : Sort u} when the user
-- omits the argument; first-order unification solves them.
-- Universe-level metavariables are NOT yet supported, so the user
-- must still pin `.{u}` explicitly (else u is left as a free param —
-- handled but only when the level is otherwise determined).

def id_impl.{u} {α : Sort u} (x : α) : α := x

-- The user omits α; the elaborator inserts a meta and unifies it
-- against the type of `3` (which is `Nat`).  No explicit `Nat`!
def id_three : Nat := id_impl.{1} 3

theorem id_3_eq_3 : Eq.{1} Nat id_three 3 :=
  Eq.refl.{1} Nat 3

-- Two implicit binders solved from two explicit args
def first_of_pair.{u, v} {α : Sort u} {β : Sort v} (a : α) (b : β) : α := a

def example_first : Nat := first_of_pair.{1, 1} 42 Bool.true

theorem first_eq_42 : Eq.{1} Nat example_first 42 :=
  Eq.refl.{1} Nat 42

-- A more interesting one: implicit gets pinned by the SECOND arg
def const_first.{u} {α : Sort u} (a : α) (b : α) : α := a

def two_or_three : Nat := const_first.{1} 2 3

theorem two_or_three_eq_2 : Eq.{1} Nat two_or_three 2 :=
  Eq.refl.{1} Nat 2
