-- More Nat.le lemmas, building on nat_le.lean's `Nat.le_refl` and
-- `Nat.le_trans`.  We can't use the `induction` tactic on Nat.le proofs
-- directly (Nat.le is indexed and the tactic bails on those), so we
-- either:
--   (a) drive Nat.le.rec by hand for proofs that case-split on a
--       Nat.le hypothesis, or
--   (b) `induction` on a Nat *argument* when that's enough.

-- ============================================================
-- Nat.le_succ: n ≤ succ n.  One-liner via step + refl.
-- ============================================================

theorem Nat.le_succ (n : Nat) : Nat.le n (Nat.succ n) :=
  Nat.le.step n n (Nat.le.refl n)

example : Nat.le 4 5 := Nat.le_succ 4

-- ============================================================
-- Nat.le_succ_of_le: n ≤ m → n ≤ succ m.  Direct ctor application.
-- ============================================================

theorem Nat.le_succ_of_le (n m : Nat) (h : Nat.le n m) :
    Nat.le n (Nat.succ m) :=
  Nat.le.step n m h

-- ============================================================
-- Nat.zero_le: 0 ≤ n for all n.  Induction on n (the Nat, not a proof).
-- Base: 0 ≤ 0 via Nat.le.refl.
-- Step: ih : 0 ≤ k, want 0 ≤ succ k via Nat.le.step.
-- ============================================================

theorem Nat.zero_le (n : Nat) : Nat.le 0 n :=
  by induction n;
     -- base
     apply Nat.le.refl;
     -- step
     intro k; intro ih;
     apply Nat.le.step;
     exact ih

example : Nat.le 0 7 := Nat.zero_le 7

-- ============================================================
-- Nat.succ_le_succ: n ≤ m → succ n ≤ succ m.  Induct on the proof
-- using Nat.le.rec directly (indexed; the tactic doesn't support it).
-- Motive(k, _) := Nat.le (succ n) (succ k).
--   refl case (k = n): need Nat.le (succ n) (succ n).  Refl.
--   step case from ih : Nat.le (succ n) (succ k): step ih.
-- ============================================================

theorem Nat.succ_le_succ (n m : Nat) (h : Nat.le n m) :
    Nat.le (Nat.succ n) (Nat.succ m) :=
  @Nat.le.rec.{0} n
    (fun (k : Nat) (_ : Nat.le n k) =>
       Nat.le (Nat.succ n) (Nat.succ k))
    (Nat.le.refl (Nat.succ n))
    (fun (k : Nat) (_h : Nat.le n k)
         (ih : Nat.le (Nat.succ n) (Nat.succ k)) =>
       Nat.le.step (Nat.succ n) (Nat.succ k) ih)
    m h

example : Nat.le 4 6 :=
  Nat.succ_le_succ 3 5
    (Nat.le.step 3 4 (Nat.le.step 3 3 (Nat.le.refl 3)))

-- ============================================================
-- Nat.lt_succ_self: n < succ n.  Definitionally Nat.le (succ n) (succ n).
-- ============================================================

theorem Nat.lt_succ_self (n : Nat) : Nat.lt n (Nat.succ n) :=
  Nat.le.refl (Nat.succ n)

example : Nat.lt 5 6 := Nat.lt_succ_self 5

-- ============================================================
-- Nat.lt_succ_of_lt: n < m → n < succ m.  Direct step.
-- Nat.lt n m unfolds to Nat.le (succ n) m, so this is exactly the
-- step constructor.
-- ============================================================

theorem Nat.lt_succ_of_lt (n m : Nat) (h : Nat.lt n m) :
    Nat.lt n (Nat.succ m) :=
  Nat.le.step (Nat.succ n) m h

example : Nat.lt 3 7 :=
  Nat.lt_succ_of_lt 3 6
    (Nat.lt_succ_of_lt 3 5
      (Nat.lt_succ_of_lt 3 4
        (Nat.lt_succ_self 3)))

-- ============================================================
-- Nat.le_of_lt: n < m → n ≤ m.  Drop a succ from a Nat.le (succ n) m
-- proof via Nat.le.rec.  Motive(k, _) := Nat.le n k.
--   refl case (k = succ n): need Nat.le n (succ n).  That's Nat.le_succ.
--   step case from ih : Nat.le n k: ih + step gives Nat.le n (succ k).
-- ============================================================

theorem Nat.le_of_lt (n m : Nat) (h : Nat.lt n m) : Nat.le n m :=
  @Nat.le.rec.{0} (Nat.succ n)
    (fun (k : Nat) (_ : Nat.le (Nat.succ n) k) => Nat.le n k)
    (Nat.le_succ n)
    (fun (k : Nat) (_h : Nat.le (Nat.succ n) k) (ih : Nat.le n k) =>
       Nat.le.step n k ih)
    m h

example : Nat.le 3 7 :=
  Nat.le_of_lt 3 7
    (Nat.lt_succ_of_lt 3 6
      (Nat.lt_succ_of_lt 3 5
        (Nat.lt_succ_of_lt 3 4
          (Nat.lt_succ_self 3))))
