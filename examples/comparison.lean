-- Sub class, Mul class, all working through instance synthesis.

class Add.{u} (a : Sort u) : Sort u where
  add : a -> a -> a

class Sub.{u} (a : Sort u) : Sort u where
  sub : a -> a -> a

class Mul.{u} (a : Sort u) : Sort u where
  mul : a -> a -> a

instance addNat : Add.{1} Nat := Add.mk.{1} Nat Nat.add
instance mulNat : Mul.{1} Nat := Mul.mk.{1} Nat Nat.mul

-- Subtraction for Nat
def Nat.sub_toy (m n : Nat) : Nat :=
  match n : Nat with
  | Nat.zero => m
  | Nat.succ k => Nat.pred (Nat.sub_toy m k)

instance subNat : Sub.{1} Nat := Sub.mk.{1} Nat Nat.sub_toy

infixl:65 + Add.add
infixl:65 - Sub.sub
infixl:70 * Mul.mul

def expr1 : Nat := 2 * 3 + 4
example : Eq.{1} Nat expr1 10 := Eq.refl.{1} Nat 10

def sub_demo : Nat := 10 - 3
example : Eq.{1} Nat sub_demo 7 := Eq.refl.{1} Nat 7

-- A polymorphic function over all three classes; instances synthesised
def poly.{u} {a : Sort u}
    [Add.{u} a] [Sub.{u} a] [Mul.{u} a] (x y : a) : a :=
  x * y + x - y

def example_poly : Nat := poly 3 2
example : Eq.{1} Nat example_poly 7 := Eq.refl.{1} Nat 7
