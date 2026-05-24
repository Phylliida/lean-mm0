-- Decidable equality on Nat, using nat_no_confuse / succ_ne_zero /
-- succ_inj from nat_inj.lean.
--
-- We use Nat.rec directly (rather than `match` with structural-recursion
-- sugar) because the recursive call needs BOTH arguments to decrease,
-- which the def-by-match sugar doesn't support.  Phrasing the motive as
-- `fun n => Π m, Decidable (Eq n m)` lets the IH be a function that we
-- apply to any new m.

def Nat.decEq (n : Nat) : (m : Nat) -> Decidable (Eq.{1} Nat n m) :=
  @Nat.rec.{1}
    (fun (x : Nat) => (m : Nat) -> Decidable (Eq.{1} Nat x m))
    -- zero case: Π m, Decidable (Eq zero m)
    (fun (m : Nat) =>
      match (motive := fun (y : Nat) => Decidable (Eq.{1} Nat Nat.zero y)) m with
      | Nat.zero =>
        Decidable.isTrue (Eq.{1} Nat Nat.zero Nat.zero)
          (Eq.refl.{1} Nat Nat.zero)
      | Nat.succ k =>
        Decidable.isFalse (Eq.{1} Nat Nat.zero (Nat.succ k))
          (fun (h : Eq.{1} Nat Nat.zero (Nat.succ k)) =>
            succ_ne_zero k (@Eq.symm.{1} Nat Nat.zero (Nat.succ k) h)))
    -- succ case: IH : Π m, Decidable (Eq k m); produce Π m, Decidable (Eq (succ k) m)
    (fun (k : Nat) (ih : (m : Nat) -> Decidable (Eq.{1} Nat k m)) =>
      fun (m : Nat) =>
        match (motive := fun (y : Nat) => Decidable (Eq.{1} Nat (Nat.succ k) y)) m with
        | Nat.zero =>
          Decidable.isFalse (Eq.{1} Nat (Nat.succ k) Nat.zero) (succ_ne_zero k)
        | Nat.succ j =>
          @Decidable.rec.{1} (Eq.{1} Nat k j)
            (fun (_ : Decidable (Eq.{1} Nat k j)) =>
               Decidable (Eq.{1} Nat (Nat.succ k) (Nat.succ j)))
            (fun (h_neg : Not (Eq.{1} Nat k j)) =>
              Decidable.isFalse (Eq.{1} Nat (Nat.succ k) (Nat.succ j))
                (fun (h : Eq.{1} Nat (Nat.succ k) (Nat.succ j)) =>
                  h_neg (succ_inj k j h)))
            (fun (h_pos : Eq.{1} Nat k j) =>
              Decidable.isTrue (Eq.{1} Nat (Nat.succ k) (Nat.succ j))
                (@Eq.rec.{1, 0} Nat k
                  (fun (x : Nat) (_ : Eq.{1} Nat k x) =>
                     Eq.{1} Nat (Nat.succ k) (Nat.succ x))
                  (Eq.refl.{1} Nat (Nat.succ k))
                  j h_pos))
            (ih j))
    n

example : Eq.{1} Nat (@ite.{1} Nat (Eq.{1} Nat 3 3) (Nat.decEq 3 3) 1 2) 1 := by rfl
example : Eq.{1} Nat (@ite.{1} Nat (Eq.{1} Nat 3 4) (Nat.decEq 3 4) 1 2) 2 := by rfl
example : Eq.{1} Nat (@ite.{1} Nat (Eq.{1} Nat 5 5) (Nat.decEq 5 5) 99 0) 99 := by rfl
