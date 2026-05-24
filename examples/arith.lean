-- Real arithmetic syntax: class + instance + infix notation.
-- This is the closest the prototype gets to actual Lean 4 source.

class Add.{u} (a : Sort u) : Sort u where
  add : a -> a -> a

instance addNat : Add.{1} Nat :=
  Add.mk.{1} Nat Nat.add

-- Bind the symbol `+` to a (binary, prefix-rewritten) call.  We have
-- no precedence/parens machinery, so `+` sits at one level just below
-- function application.  Resolves through instance synthesis.
infix + Add.add

-- Now this looks just like Lean.
def four : Nat := 1 + 3

theorem four_eq : Eq.{1} Nat four 4 :=
  Eq.refl.{1} Nat 4

-- Polymorphic functions over Add
def quad.{u} {a : Sort u} [_inst : Add.{u} a] (x : a) : a := x + x + x + x

def twelve : Nat := quad 3

theorem twelve_eq : Eq.{1} Nat twelve 12 :=
  Eq.refl.{1} Nat 12

-- Chained additions
def sixteen : Nat := 1 + 2 + 3 + 4 + 5 + 1
theorem sixteen_eq : Eq.{1} Nat sixteen 16 :=
  Eq.refl.{1} Nat 16
