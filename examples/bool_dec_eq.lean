-- Decidable equality on Bool.  Finite (just 4 cases), so no recursion
-- needed — only the no-confusion principle to handle the mismatch
-- cases (true ≠ false and vice versa).

-- No-confusion predicate on Bool: True at true, False at false.
def bool_no_confuse (b : Bool) : Prop :=
  match b : Prop with
  | Bool.true => True
  | Bool.false => False

-- true ≠ false.
def true_ne_false (h : Eq.{1} Bool Bool.true Bool.false) : False :=
  @Eq.rec.{1, 0} Bool Bool.true
    (fun (b : Bool) (_ : Eq.{1} Bool Bool.true b) => bool_no_confuse b)
    True.intro
    Bool.false h

-- false ≠ true (derived by Eq.symm).
def false_ne_true (h : Eq.{1} Bool Bool.false Bool.true) : False :=
  true_ne_false (@Eq.symm.{1} Bool Bool.false Bool.true h)

def Bool.decEq (a b : Bool) : Decidable (Eq.{1} Bool a b) :=
  match (motive := fun (x : Bool) => Decidable (Eq.{1} Bool x b)) a with
  | Bool.true =>
    (match (motive := fun (y : Bool) => Decidable (Eq.{1} Bool Bool.true y)) b with
     | Bool.true =>
       Decidable.isTrue (Eq.{1} Bool Bool.true Bool.true)
         (Eq.refl.{1} Bool Bool.true)
     | Bool.false =>
       Decidable.isFalse (Eq.{1} Bool Bool.true Bool.false) true_ne_false)
  | Bool.false =>
    (match (motive := fun (y : Bool) => Decidable (Eq.{1} Bool Bool.false y)) b with
     | Bool.true =>
       Decidable.isFalse (Eq.{1} Bool Bool.false Bool.true) false_ne_true
     | Bool.false =>
       Decidable.isTrue (Eq.{1} Bool Bool.false Bool.false)
         (Eq.refl.{1} Bool Bool.false))

example : Eq.{1} Nat (@ite.{1} Nat (Eq.{1} Bool Bool.true Bool.true)
                        (Bool.decEq Bool.true Bool.true) 1 2) 1 := by rfl
example : Eq.{1} Nat (@ite.{1} Nat (Eq.{1} Bool Bool.true Bool.false)
                        (Bool.decEq Bool.true Bool.false) 1 2) 2 := by rfl
example : Eq.{1} Nat (@ite.{1} Nat (Eq.{1} Bool Bool.false Bool.false)
                        (Bool.decEq Bool.false Bool.false) 1 2) 1 := by rfl
