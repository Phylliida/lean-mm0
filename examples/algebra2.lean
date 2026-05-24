-- Algebra with multiple operator classes — Add, Mul — and inferred
-- instances.  All the infrastructure (class, instance synth, infix,
-- implicit/level meta inference) cooperating.

class Add.{u} (a : Sort u) : Sort u where
  add : a -> a -> a

class Mul.{u} (a : Sort u) : Sort u where
  mul : a -> a -> a

instance addNat : Add.{1} Nat := Add.mk.{1} Nat Nat.add
instance mulNat : Mul.{1} Nat := Mul.mk.{1} Nat Nat.mul

infixl:65 + Add.add
infixl:70 * Mul.mul

-- Real Lean-style precedence: `*` binds tighter than `+`.
def expr1 : Nat := (1 + 2) * 3
theorem expr1_eq : Eq.{1} Nat expr1 9 := Eq.refl.{1} Nat 9

-- No parens needed for `2*2 + 3*3` thanks to precedence
def expr2 : Nat := 2 * 2 + 3 * 3
theorem expr2_eq : Eq.{1} Nat expr2 13 := Eq.refl.{1} Nat 13

def expr3 : Nat := 1 + 2 * 3 + 4
theorem expr3_eq : Eq.{1} Nat expr3 11 := Eq.refl.{1} Nat 11

-- A polymorphic function over BOTH classes.  Instance synthesis
-- inserts both [Add a] and [Mul a].
def squareThenAdd.{u}
    {a : Sort u} [Add.{u} a] [Mul.{u} a] (x y : a) : a :=
  x * x + y * y

def hypot_sq : Nat := squareThenAdd 3 4
theorem hypot_eq : Eq.{1} Nat hypot_sq 25 := Eq.refl.{1} Nat 25
