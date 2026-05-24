-- Demonstrate `match` expressions, compiled to recursor invocations.
-- Only Nat and Bool scrutinees are supported in this prototype.

def is_zero (n : Nat) : Bool :=
  match n : Bool with
  | Nat.zero => Bool.true
  | Nat.succ k => Bool.false

def pred (n : Nat) : Nat :=
  match n : Nat with
  | Nat.zero => Nat.zero
  | Nat.succ k => k

def boolNot (b : Bool) : Bool :=
  match b : Bool with
  | Bool.false => Bool.true
  | Bool.true => Bool.false

-- Computation through the verifier
theorem is_zero_0 : Eq.{1} Bool (is_zero 0) Bool.true := Eq.refl.{1} Bool Bool.true
theorem is_zero_3 : Eq.{1} Bool (is_zero 3) Bool.false := Eq.refl.{1} Bool Bool.false
theorem pred_7 : Eq.{1} Nat (pred 7) 6 := Eq.refl.{1} Nat 6
theorem not_true_match : Eq.{1} Bool (boolNot Bool.true) Bool.false :=
  Eq.refl.{1} Bool Bool.false
