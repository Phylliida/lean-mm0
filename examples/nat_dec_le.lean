-- Decidable ordering on Nat.  Mirrors nat_dec_eq.lean's structure:
-- outer Nat.rec with motive `λ n. Π m, Decidable (Le n m)`, inner
-- `match` on m, then Decidable.rec to case-split on the IH.  Relies
-- on:
--   Nat.zero_le, Nat.not_succ_le_zero, Nat.succ_le_succ
--      — from nat_le_more.lean / index_unif.lean
--   Nat.pred_le_pred
--      — from nat_le_chain.lean

def Nat.decLe (n : Nat) : (m : Nat) -> Decidable (Nat.le n m) :=
  @Nat.rec.{1}
    (fun (x : Nat) => (m : Nat) -> Decidable (Nat.le x m))
    -- zero case: Π m, Decidable (Le 0 m).  Always true via zero_le.
    (fun (m : Nat) =>
      Decidable.isTrue (Nat.le Nat.zero m) (Nat.zero_le m))
    -- succ case: IH : Π m, Decidable (Le k m); produce
    --             Π m, Decidable (Le (succ k) m).
    (fun (k : Nat) (ih : (m : Nat) -> Decidable (Nat.le k m)) =>
      fun (m : Nat) =>
        match (motive :=
                 fun (y : Nat) => Decidable (Nat.le (Nat.succ k) y)) m with
        | Nat.zero =>
          Decidable.isFalse (Nat.le (Nat.succ k) Nat.zero)
            (Nat.not_succ_le_zero k)
        | Nat.succ j =>
          @Decidable.rec.{1} (Nat.le k j)
            (fun (_ : Decidable (Nat.le k j)) =>
               Decidable (Nat.le (Nat.succ k) (Nat.succ j)))
            (fun (h_neg : Not (Nat.le k j)) =>
              Decidable.isFalse (Nat.le (Nat.succ k) (Nat.succ j))
                (fun (h : Nat.le (Nat.succ k) (Nat.succ j)) =>
                  h_neg (Nat.pred_le_pred k j h)))
            (fun (h_pos : Nat.le k j) =>
              Decidable.isTrue (Nat.le (Nat.succ k) (Nat.succ j))
                (Nat.succ_le_succ k j h_pos))
            (ih j))
    n

-- Nat.lt unfolds to Nat.le (succ n) m, so decLt is just decLe shifted.
def Nat.decLt (n m : Nat) : Decidable (Nat.lt n m) :=
  Nat.decLe (Nat.succ n) m

-- Sanity: use them in ite to compute branches at the kernel.
example : Eq.{1} Nat
    (@ite.{1} Nat (Nat.le 3 5) (Nat.decLe 3 5) 1 2) 1 := by rfl

example : Eq.{1} Nat
    (@ite.{1} Nat (Nat.le 5 3) (Nat.decLe 5 3) 1 2) 2 := by rfl

example : Eq.{1} Nat
    (@ite.{1} Nat (Nat.lt 3 4) (Nat.decLt 3 4) 99 0) 99 := by rfl

example : Eq.{1} Nat
    (@ite.{1} Nat (Nat.lt 4 4) (Nat.decLt 4 4) 99 0) 0 := by rfl

-- Register as instances for the `if c then a else b` sugar.
-- Args must be implicit for synthesis to pick them up.
instance instDecidableNatLe {n m : Nat} : Decidable (Nat.le n m) :=
  Nat.decLe n m

instance instDecidableNatLt {n m : Nat} : Decidable (Nat.lt n m) :=
  Nat.decLt n m

def min (a b : Nat) : Nat :=
  if Nat.le a b then a else b

example : Eq.{1} Nat (min 3 5) 3 := by rfl
example : Eq.{1} Nat (min 7 2) 2 := by rfl
example : Eq.{1} Nat (min 4 4) 4 := by rfl
