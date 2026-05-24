-- Demonstrate Nat.le (the indexed Prop) through the parser.

-- 3 ≤ 3 by reflexivity
def le_3_3 : Nat.le 3 3 :=
  Nat.le.refl 3

-- 3 ≤ 4 = step 3 3 (refl 3)
def le_3_4 : Nat.le 3 4 :=
  Nat.le.step 3 3 (Nat.le.refl 3)

-- 0 ≤ 2, built up by two `step`s from refl
def le_0_2 : Nat.le 0 2 :=
  Nat.le.step 0 1
    (Nat.le.step 0 0 (Nat.le.refl 0))

-- Polymorphic in the "chain length" — here, demonstrated as a function
-- that consumes a Nat.le proof and produces another by one more step
def succ_le (n : Nat) (m : Nat) (h : Nat.le n m) : Nat.le n (Nat.succ m) :=
  Nat.le.step n m h
