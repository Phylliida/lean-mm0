-- Real typeclass usage: `structure Magma` with a true projection
-- `Magma.op`.  Because the projection is generated via the recursor,
-- the verifier CAN ι-reduce `Magma.op (Magma.mk Nat.add) 3 3` to
-- `Nat.add 3 3`, and then β/δ-reduce that to `6`.

structure Magma.{u} (a : Sort u) : Sort u where
  op : a -> a -> a

instance natMagma : Magma.{1} Nat :=
  Magma.mk.{1} Nat Nat.add

-- A polymorphic function that uses [m : Magma α].  Both `α` and `m`
-- are inferred — `α` from `x`, `m` by instance synthesis.
def double.{u} {a : Sort u} [m : Magma.{u} a] (x : a) : a :=
  Magma.op.{u} a m x x

-- No instance argument supplied.
def six : Nat := double 3

-- THE WIN: this only verifies because the projection's ι-rule fires
-- through the verifier, reducing `Magma.op (Magma.mk Nat.add) 3 3` to 6.
theorem six_eq_six : Eq.{1} Nat six 6 :=
  Eq.refl.{1} Nat 6

-- Instance-implicit propagated through nested calls
def quadruple.{u} {a : Sort u} [m : Magma.{u} a] (x : a) : a :=
  double (double x)

def twelve : Nat := quadruple 3

theorem twelve_eq : Eq.{1} Nat twelve 12 :=
  Eq.refl.{1} Nat 12
