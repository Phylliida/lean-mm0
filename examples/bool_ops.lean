-- Small Bool theory: not, and, or, with a couple round-trip lemmas.

def Bool.not (b : Bool) : Bool :=
  match b : Bool with
  | Bool.true => Bool.false
  | Bool.false => Bool.true

def Bool.and (a b : Bool) : Bool :=
  match a : Bool with
  | Bool.true => b
  | Bool.false => Bool.false

def Bool.or (a b : Bool) : Bool :=
  match a : Bool with
  | Bool.true => Bool.true
  | Bool.false => b

-- Double negation is the identity.  Dependent match — each arm reduces
-- by computation to the corresponding refl.
def Bool.not_not (b : Bool) : Eq.{1} Bool (Bool.not (Bool.not b)) b :=
  match (motive := fun (x : Bool) =>
                    Eq.{1} Bool (Bool.not (Bool.not x)) x) b with
  | Bool.true  => Eq.refl.{1} Bool Bool.true
  | Bool.false => Eq.refl.{1} Bool Bool.false

example : Eq.{1} Bool (Bool.not Bool.true) Bool.false := by rfl
example : Eq.{1} Bool (Bool.and Bool.true Bool.false) Bool.false := by rfl
example : Eq.{1} Bool (Bool.or Bool.true Bool.false) Bool.true := by rfl
example : Eq.{1} Bool (Bool.not (Bool.not Bool.true)) Bool.true := Bool.not_not Bool.true
