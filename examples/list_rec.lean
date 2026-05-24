-- Structural recursion on List.  Same machinery as Nat recursion,
-- generalised through the recursor with rec_arg_positions.

class Add.{u} (a : Sort u) : Sort u where
  add : a -> a -> a

instance addNat : Add.{1} Nat := Add.mk.{1} Nat Nat.add

infixl:65 + Add.add

def length.{u} {a : Sort u} (xs : List.{u} a) : Nat :=
  match xs : Nat with
  | List.nil => 0
  | List.cons h t => Nat.succ (length t)

def empty : List.{1} Nat := List.nil.{1} Nat
def three_nats : List.{1} Nat :=
  List.cons.{1} Nat 7 (List.cons.{1} Nat 8 (List.cons.{1} Nat 9 empty))

example : Eq.{1} Nat (length empty) 0 := Eq.refl.{1} Nat 0
example : Eq.{1} Nat (length three_nats) 3 := Eq.refl.{1} Nat 3

def sum_list (xs : List.{1} Nat) : Nat :=
  match xs : Nat with
  | List.nil => 0
  | List.cons h t => h + sum_list t

example : Eq.{1} Nat (sum_list empty) 0 := Eq.refl.{1} Nat 0
example : Eq.{1} Nat (sum_list three_nats) 24 := Eq.refl.{1} Nat 24
