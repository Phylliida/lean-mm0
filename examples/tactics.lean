-- Tiny tactic monad.  Three tactics:
--   exact e   -- solve the current goal with `e`
--   rfl       -- solve an Eq-goal whose sides are def-equal
--   intro x   -- when the goal is `Π x : T, U`, build a `λ x : T, _`
-- and `;` for sequencing.

example : Eq.{1} Nat 4 4 := by rfl
example : Eq.{1} Nat (Nat.add 2 3) 5 := by rfl
example : Nat := by exact 7

-- intro consumes a Pi binder
def id_via_tac : Nat -> Nat := by intro x; exact x
example : Eq.{1} Nat (id_via_tac 5) 5 := by rfl

def const_via_tac : Nat -> Nat -> Nat := by intro x; intro y; exact x
example : Eq.{1} Nat (const_via_tac 7 8) 7 := by rfl

def id_poly_via_tac.{u} {a : Sort u} : a -> a := by intro x; exact x
example : Eq.{1} Nat (@id_poly_via_tac.{1} Nat 42) 42 := by rfl

example : Eq.{1} Nat (Nat.add 3 5) (Nat.add 5 3) := by rfl
