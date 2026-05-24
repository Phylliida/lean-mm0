-- Structural recursion over Nat: the compiler detects that the body
-- is a top-level `match` on the recursive arg and rewrites recursive
-- calls to use the recursor's IH.

class Mul.{u} (a : Sort u) : Sort u where
  mul : a -> a -> a

instance mulNat : Mul.{1} Nat := Mul.mk.{1} Nat Nat.mul

infixl:70 * Mul.mul

-- Recursive definition.  No `fix`-point or `WellFounded` machinery;
-- the elaborator compiles this to Nat.rec.
def factorial (n : Nat) : Nat :=
  match n : Nat with
  | Nat.zero => 1
  | Nat.succ k => (Nat.succ k) * factorial k

example : Eq.{1} Nat (factorial 0) 1 := Eq.refl.{1} Nat 1
example : Eq.{1} Nat (factorial 1) 1 := Eq.refl.{1} Nat 1
example : Eq.{1} Nat (factorial 3) 6 := Eq.refl.{1} Nat 6
example : Eq.{1} Nat (factorial 5) 120 := Eq.refl.{1} Nat 120

-- Another recursive function: sum of 1..n
class Add.{u} (a : Sort u) : Sort u where
  add : a -> a -> a

instance addNat : Add.{1} Nat := Add.mk.{1} Nat Nat.add

infixl:65 + Add.add

def sum_up_to (n : Nat) : Nat :=
  match n : Nat with
  | Nat.zero => 0
  | Nat.succ k => (Nat.succ k) + sum_up_to k

example : Eq.{1} Nat (sum_up_to 0) 0 := Eq.refl.{1} Nat 0
example : Eq.{1} Nat (sum_up_to 5) 15 := Eq.refl.{1} Nat 15
example : Eq.{1} Nat (sum_up_to 10) 55 := Eq.refl.{1} Nat 55
