-- A small algebra-flavoured example demonstrating that the prototype
-- can handle declarations beyond the trivial cases.

-- ---- functions ----
def Nat_succ_fn : Nat -> Nat :=
  fun (n : Nat) => Nat.succ n

def square : Nat -> Nat :=
  fun (n : Nat) => Nat.mul n n

-- ---- computation through the verifier ----
theorem square_4_eq_16 : Eq.{1} Nat (square 4) 16 :=
  Eq.refl.{1} Nat 16

theorem succ_5_eq_6 : Eq.{1} Nat (Nat_succ_fn 5) 6 :=
  Eq.refl.{1} Nat 6

-- ---- a small associative property witnessed by computation ----
theorem add_assoc_3_4_5 :
    Eq.{1} Nat
      (Nat.add (Nat.add 3 4) 5)
      (Nat.add 3 (Nat.add 4 5)) :=
  Eq.refl.{1} Nat 12

-- ---- using Vec ----
def example_vec : Vec.{1} Nat 3 :=
  Vec.cons.{1} Nat 2 10
    (Vec.cons.{1} Nat 1 20
      (Vec.cons.{1} Nat 0 30 (Vec.nil.{1} Nat)))

-- ---- using Sigma ----
def first_three : Sigma.{1, 1} Nat (fun (_ : Nat) => Nat) :=
  Sigma.mk.{1, 1} Nat (fun (_ : Nat) => Nat) 0
    (Nat.add 1 2)

-- ---- using Option ----
def some_seven : Option.{1} Nat :=
  Option.some.{1} Nat 7

-- ---- using Int ----
def neg_one_int : Int :=
  Int.negSucc 0

def fifty_int : Int :=
  Int.ofNat 50

-- ---- multi-binder shorthand ----
def add_three (a b c : Nat) : Nat := Nat.add (Nat.add a b) c

theorem add_three_1_2_3 : Eq.{1} Nat (add_three 1 2 3) 6 :=
  Eq.refl.{1} Nat 6
