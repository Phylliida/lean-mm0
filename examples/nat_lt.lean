-- Nat.lt as `Nat.le (succ n) m`.  Standard definition.

def Nat.lt (n m : Nat) : Prop := Nat.le (Nat.succ n) m

-- 3 < 5  =  Nat.le 4 5  via one step from Nat.le.refl 4
example : Nat.lt 3 5 := Nat.le.step 4 4 (Nat.le.refl 4)

-- 0 < 1 directly
example : Nat.lt 0 1 := Nat.le.refl 1

-- lt is reducible to le, so transitivity transfers immediately
def Nat.lt_le (a b c : Nat) (hab : Nat.lt a b) (hbc : Nat.le b c) : Nat.lt a c :=
  Nat.le_trans (Nat.succ a) b c hab hbc
