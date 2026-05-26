-- The `simp` tactic.  Iterates rewriting the goal with the listed Eq
-- proofs until no equation matches, then tries `rfl`.  If rfl closes
-- the simplified goal, the simp is fully discharged; otherwise the
-- simplified goal remains as a subgoal.
--
-- Bounded to 200 iterations to keep loops (e.g. with commutativity
-- lemmas that can oscillate) from spinning forever.

-- ============================================================
-- Trivial: rfl-only simp.  Empty equation list; just tries rfl.
-- ============================================================

theorem trivial_simp (n : Nat) : Eq.{1} Nat n n :=
  by simp []

-- ============================================================
-- One-shot: simp [h] where h : a = b reduces the goal that depends
-- on a to one that depends on b, then rfl.
-- ============================================================

theorem one_simp (n m : Nat) (h : Eq.{1} Nat n m) :
    Eq.{1} Nat (Nat.succ n) (Nat.succ m) :=
  by simp [h]

-- ============================================================
-- A chain of three rewrites: `add 1 n = succ n` proved by simp
-- with succ_add (lifts succ across +), zero_add (drops a leading 0+).
-- This is exactly the proof of `add_one` from nat_lemmas.lean, but
-- the user just hands simp the lemmas and lets it find the chain.
-- ============================================================

theorem add_one_via_simp (n : Nat) :
    Eq.{1} Nat (Nat.add 1 n) (Nat.succ n) :=
  by simp [succ_add 0 n, zero_add n]

-- ============================================================
-- simp with multiple lemmas to discharge a small algebraic identity:
-- `n + 0 = n` is by-refl, but `n * 1` and `n * 0` are too, so
-- simp [] (just rfl) handles a few automatically.
-- ============================================================

theorem mul_zero_via_simp (n : Nat) : Eq.{1} Nat (Nat.mul n 0) 0 :=
  by simp []

theorem add_zero_via_simp (n : Nat) : Eq.{1} Nat (Nat.add n 0) n :=
  by simp []

-- ============================================================
-- A two-step rewrite chain through transposed lemmas.  Goal:
--   1 + n = succ n
-- Equations:
--   succ_add 0 n : succ 0 + n = succ (0 + n)        -- LHS appears
--   zero_add n  : 0 + n = n                          -- after first rewrite
-- After both, goal is succ n = succ n, closed by rfl.
-- ============================================================

example : Eq.{1} Nat (Nat.add 1 5) 6 := add_one_via_simp 5

-- ============================================================
-- simp followed by an explicit close.  When the simplified goal
-- isn't def-equally true, simp leaves it as a subgoal for the
-- subsequent tactic.  Here we simp with one lemma and leave the
-- final equality for `apply Eq.refl` to discharge.
-- ============================================================

theorem simp_then_apply (n m : Nat) (h : Eq.{1} Nat n m) :
    Eq.{1} Nat (Nat.succ n) (Nat.succ m) :=
  by simp [h]
