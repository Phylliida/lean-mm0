-- Polymorphic List operations: map, append.
-- Tests multi-arg structural recursion (the rec arg is the LAST arg).

-- map
def map.{u, v} {a : Sort u} {b : Sort v}
    (f : a -> b) (xs : List.{u} a) : List.{v} b :=
  match xs : List.{v} b with
  | List.nil => List.nil.{v} b
  | List.cons h t => List.cons.{v} b (f h) (map f t)

def my_nats : List.{1} Nat :=
  List.cons.{1} Nat 1
    (List.cons.{1} Nat 2
      (List.cons.{1} Nat 3 (List.nil.{1} Nat)))

-- @-syntax to disable implicit insertion and supply all args.
def doubled : List.{1} Nat :=
  @map.{1, 1} Nat Nat (fun (n : Nat) => Nat.mul n 2) my_nats

-- length still works (single-arg recursion)
def length.{u} {a : Sort u} (xs : List.{u} a) : Nat :=
  match xs : Nat with
  | List.nil => 0
  | List.cons h t => Nat.succ (length t)

-- map preserves length
example : Eq.{1} Nat (@length.{1} Nat doubled) 3 := Eq.refl.{1} Nat 3
example : Eq.{1} Nat (@length.{1} Nat my_nats) 3 := Eq.refl.{1} Nat 3

-- append: rec on the FIRST arg (the part that's structurally consumed)
def append.{u} {a : Sort u}
    (xs : List.{u} a) (ys : List.{u} a) : List.{u} a :=
  match xs : List.{u} a with
  | List.nil => ys
  | List.cons h t => List.cons.{u} a h (append t ys)

def joined : List.{1} Nat := @append.{1} Nat my_nats my_nats
example : Eq.{1} Nat (@length.{1} Nat joined) 6 := Eq.refl.{1} Nat 6
