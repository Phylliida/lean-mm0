-- Structure inheritance via `extends`.  A child class gets a synthetic
-- field per parent (named `toParent`) plus its own fields.

class Add.{u} (a : Sort u) : Sort u where
  add : a -> a -> a

class Mul.{u} (a : Sort u) : Sort u where
  mul : a -> a -> a

-- A SemiRing has both an Add and a Mul (plus a `zero` of its own).
class SemiRing.{u} (a : Sort u) : Sort u extends Add.{u} a, Mul.{u} a where
  (zero : a)

instance addNat : Add.{1} Nat := Add.mk.{1} Nat Nat.add
instance mulNat : Mul.{1} Nat := Mul.mk.{1} Nat Nat.mul

-- Build a SemiRing for Nat by composing parent instances.
instance srNat : SemiRing.{1} Nat :=
  SemiRing.mk.{1} Nat addNat mulNat Nat.zero

-- Use @-syntax to call projections without implicit-arg inference.
def get_add : Add.{1} Nat := @SemiRing.toAdd.{1} Nat srNat
def get_mul : Mul.{1} Nat := @SemiRing.toMul.{1} Nat srNat
def get_zero : Nat := @SemiRing.zero.{1} Nat srNat

example : Eq.{1} Nat (@Add.add.{1} Nat get_add 2 3) 5 :=
  Eq.refl.{1} Nat 5

example : Eq.{1} Nat (@Mul.mul.{1} Nat get_mul 4 5) 20 :=
  Eq.refl.{1} Nat 20

example : Eq.{1} Nat get_zero 0 := Eq.refl.{1} Nat 0
