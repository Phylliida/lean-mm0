-- The `have h : T := e` tactic.  Introduces an intermediate
-- hypothesis named h of type T (proved by e), then continues with
-- the rest of the seq.  Implemented as a deferred `Let`-wrap around
-- the main term (interleaved with intros in chronological order).

-- ============================================================
-- Trivial demo: bind a constant and use it.
-- ============================================================

def have_const : Nat :=
  by have h : Nat := 7;
     exact h

example : Eq.{1} Nat have_const 7 := by rfl

-- ============================================================
-- Have interleaved with intros: prove `Π m n, Eq (m + n) (n + m)`
-- but use a `have` to name the symmetry helper before applying it.
-- ============================================================

def have_with_intro : (m : Nat) -> (n : Nat) ->
    Eq.{1} Nat (Nat.add m n) (Nat.add n m) :=
  by intro m;
     intro n;
     have h : Eq.{1} Nat (Nat.add m n) (Nat.add n m) := add_comm m n;
     exact h

example : Eq.{1} Nat (Nat.add 3 5) (Nat.add 5 3) := have_with_intro 3 5

-- ============================================================
-- Multiple haves: build up a chain.  After each have the value is
-- in scope and visible to subsequent haves and to the final `exact`.
-- ============================================================

def have_chain (m : Nat) : Nat :=
  by have a : Nat := Nat.succ m;
     have b : Nat := Nat.succ a;
     have c : Nat := Nat.succ b;
     exact c

example : Eq.{1} Nat (have_chain 4) 7 := by rfl

-- ============================================================
-- Have inside a more complex tactic block: intro, have, apply.
-- ============================================================

theorem zero_add_via_have : (n : Nat) -> Eq.{1} Nat (Nat.add 0 n) n :=
  by intro n;
     have h : Eq.{1} Nat (Nat.add 0 n) n := zero_add n;
     exact h

example : Eq.{1} Nat (Nat.add 0 5) 5 := zero_add_via_have 5

-- ============================================================
-- `have h := e` without type annotation: the type is inferred from
-- the value at elaboration time.  Saves typing for obvious cases.
-- ============================================================

def have_no_ty : Nat :=
  by have x := 42;
     exact x

example : Eq.{1} Nat have_no_ty 42 := by rfl

-- Inferred type from a complex expression: Eq Nat (m+n) (n+m).
theorem zero_add_inferred : (n : Nat) -> Eq.{1} Nat (Nat.add 0 n) n :=
  by intro n;
     have h := zero_add n;
     exact h

example : Eq.{1} Nat (Nat.add 0 3) 3 := zero_add_inferred 3
