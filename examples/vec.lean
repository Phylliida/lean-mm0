-- Vec example: a length-indexed list, with the length function and
-- a value-level theorem `length [7,8] = 2` verified through MM0.
-- Demonstrates that the parser→kernel→emitter→MM0-verifier pipeline
-- handles indexed inductive families.

-- A 1-element vector
def my_singleton : Vec.{1} Nat 1 :=
  Vec.cons.{1} Nat 0 7 (Vec.nil.{1} Nat)

-- A 2-element vector
def my_pair : Vec.{1} Nat 2 :=
  Vec.cons.{1} Nat 1 7
    (Vec.cons.{1} Nat 0 8 (Vec.nil.{1} Nat))

-- Vec.length needs to be defined first via the parser
def Vec_length.{u} (a : Sort u) (n : Nat) (v : Vec.{u} a n) : Nat :=
  Vec.rec.{u, 1} a
    (fun (k : Nat) => fun (w : Vec.{u} a k) => Nat)
    Nat.zero
    (fun (k : Nat) => fun (x : a) => fun (t : Vec.{u} a k) => fun (ih : Nat) =>
       Nat.succ ih)
    n
    v

theorem length_singleton_is_1 :
    Eq.{1} Nat (Vec_length.{1} Nat 1 my_singleton) 1 :=
  Eq.refl.{1} Nat 1

theorem length_pair_is_2 :
    Eq.{1} Nat (Vec_length.{1} Nat 2 my_pair) 2 :=
  Eq.refl.{1} Nat 2
