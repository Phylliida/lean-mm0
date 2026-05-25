-- `cases` on indexed inductives.  The motive is non-dependent (the
-- goal stays the same in every branch — indices and the scrutinee's
-- structure are NOT exposed via specialisation).  This is much less
-- powerful than dependent indexed case analysis would be, but it
-- removes the hard bailout and is occasionally useful for proofs
-- whose conclusion doesn't depend on the indices.

-- ============================================================
-- A vacuous "from any Nat.le, derive True".  Exercises the cases
-- machinery on an indexed inductive (Nat.le has 1 param + 1 index).
-- Both branches return True.intro; the step branch can ignore its
-- IH (which also has type True).
-- ============================================================

def Nat.le_to_true (n m : Nat) (h : Nat.le n m) : True :=
  by cases h;
     -- refl case: motive m (refl m) = True
     exact True.intro;
     -- step case: take m', h', ih:True; produce True
     intro m1; intro h1; intro ih;
     exact True.intro

example : True := Nat.le_to_true 3 5
  (Nat.le.step 3 4 (Nat.le.step 3 3 (Nat.le.refl 3)))

-- ============================================================
-- `induction` on an indexed inductive: dependent motive over both
-- the indices (which must be FVars in the scrutinee's type) and the
-- scrutinee.  Each subgoal's goal is specialised to the constructor's
-- index pattern.  Limitation: hypotheses elsewhere in the context
-- that depend on an abstracted index keep their *original* types,
-- so this is most useful when the goal references the index but no
-- other hypothesis does.
--
-- Demo: `succ_le_succ` redone with the tactic.  The hand-written
-- version is in nat_le_more.lean; this one drives Nat.le.rec via the
-- tactic instead.  The motive is
--   λ k. λ h. Nat.le (succ n) (succ k)
-- so the refl branch's goal is Nat.le (succ n) (succ n) and the step
-- branch's goal is Nat.le (succ n) (succ (succ k)) with an IH of
-- type Nat.le (succ n) (succ k).
-- ============================================================

theorem Nat.succ_le_succ_via_induction (n m : Nat) (h : Nat.le n m) :
    Nat.le (Nat.succ n) (Nat.succ m) :=
  by induction h;
     -- refl: prove Nat.le (succ n) (succ n)
     apply Nat.le.refl;
     -- step: take k h_inner ih (ih : Nat.le (succ n) (succ k));
     -- prove Nat.le (succ n) (succ (succ k))
     intro k; intro h_inner; intro ih;
     apply Nat.le.step;
     exact ih

example : Nat.le 5 7 :=
  Nat.succ_le_succ_via_induction 4 6
    (Nat.le.step 4 5 (Nat.le.step 4 4 (Nat.le.refl 4)))

-- `le_succ_of_le` redone with the tactic — also a clean indexed
-- induction (the goal mentions only the abstracted index `m`).
theorem Nat.le_succ_of_le_via_induction (n m : Nat) (h : Nat.le n m) :
    Nat.le n (Nat.succ m) :=
  by induction h;
     -- refl branch: prove Nat.le n (succ n).
     apply Nat.le.step; apply Nat.le.refl;
     -- step branch: ih : Nat.le n (succ k); prove Nat.le n (succ (succ k)).
     intro k; intro h_inner; intro ih;
     apply Nat.le.step;
     exact ih

example : Nat.le 1 4 :=
  Nat.le_succ_of_le_via_induction 1 3
    (Nat.le.step 1 2 (Nat.le.step 1 1 (Nat.le.refl 1)))
