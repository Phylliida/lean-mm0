-- Basic facts about Nat.le.  Nat.le.rec has the indexed-inductive
-- signature, so we drive it by hand here (the match sugar doesn't
-- yet handle recursive indexed inductives).

-- Reflexivity is just the constructor.
def le_refl (n : Nat) : Nat.le n n := Nat.le.refl n

-- Transitivity by induction on the second hypothesis.
def le_trans (a b c : Nat) (hab : Nat.le a b) (hbc : Nat.le b c) :
    Nat.le a c :=
  @Nat.le.rec.{0} b
    (fun (k : Nat) (_ : Nat.le b k) => Nat.le a k)
    hab
    (fun (m : Nat) (_h : Nat.le b m) (ih : Nat.le a m) =>
       Nat.le.step a m ih)
    c hbc

-- Sanity: explicit chain.  3 ≤ 5 via two steps from 3 ≤ 3.
example : Nat.le 3 5 :=
  Nat.le.step 3 4 (Nat.le.step 3 3 (Nat.le.refl 3))

-- Transitivity in action.
example : Nat.le 1 5 :=
  le_trans 1 3 5
    (Nat.le.step 1 2 (Nat.le.step 1 1 (Nat.le.refl 1)))
    (Nat.le.step 3 4 (Nat.le.step 3 3 (Nat.le.refl 3)))
