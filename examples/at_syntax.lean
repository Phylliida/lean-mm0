-- `@`-syntax: turn off implicit-argument insertion at a use site.

def id_poly.{u} {a : Sort u} (x : a) : a := x

-- Normal call: implicit α is inferred from 3 : Nat
def normal : Nat := id_poly 3

-- @-call: the user supplies α explicitly
def explicit_arg : Nat := @id_poly.{1} Nat 3

theorem same : Eq.{1} Nat normal explicit_arg :=
  Eq.refl.{1} Nat 3
