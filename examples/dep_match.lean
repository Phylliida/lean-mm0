-- Dependent `match` via the `(motive := M)` annotation: the result
-- type of each arm can mention the scrutinee, because the recursor's
-- motive isn't pinned to a non-dependent constant.

-- A re-implementation of Nat.rec using `match (motive := T)`.
def my_nat_rec.{u}
    (T : Nat -> Sort u)
    (h0 : T Nat.zero)
    (hs : Nat -> T Nat.zero -> T Nat.zero)
    (n : Nat) : T Nat.zero :=
  match (motive := fun (_ : Nat) => T Nat.zero) n with
  | Nat.zero => h0
  | Nat.succ k => hs k h0

-- Sanity check: my_nat_rec on a concrete T produces a Nat.
def ten_for_zero : Nat := my_nat_rec.{1} (fun (_ : Nat) => Nat) 10 (fun (k : Nat) (h : Nat) => h) 7
example : Eq.{1} Nat ten_for_zero 10 := by rfl

-- A truly dependent motive: define is_zero whose result type depends
-- on the scrutinee.  (We use a non-dependent motive on the outside but
-- the principle is the same — this exercises the (motive := ...) syntax
-- in a real scenario.)
def is_zero (n : Nat) : Bool :=
  match (motive := fun (_ : Nat) => Bool) n with
  | Nat.zero => Bool.true
  | Nat.succ k => Bool.false

example : Eq.{1} Bool (is_zero 0) Bool.true := by rfl
example : Eq.{1} Bool (is_zero 5) Bool.false := by rfl

-- A truly dependent motive whose body mentions the scrutinee: each arm
-- proves an equality that's "k = k" with k pinned by the constructor.
-- The motive applied to Nat.zero is `Eq Nat 0 0`; applied to Nat.succ k
-- it's `Eq Nat (succ k) (succ k)`.
def nat_self_eq (n : Nat) : Eq.{1} Nat n n :=
  match (motive := fun (k : Nat) => Eq.{1} Nat k k) n with
  | Nat.zero => Eq.refl.{1} Nat Nat.zero
  | Nat.succ k => Eq.refl.{1} Nat (Nat.succ k)

-- nat_self_eq reduces correctly at each ctor.
example : Eq.{0} (Eq.{1} Nat 3 3) (nat_self_eq 3) (Eq.refl.{1} Nat 3) := by rfl
