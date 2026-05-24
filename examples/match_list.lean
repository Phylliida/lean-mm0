-- Polymorphic `match` on a List scrutinee.  Restricted: the scrutinee
-- must be closed (no outer-binder references) because we don't yet
-- thread binder types into the parser's match compiler.

def my_list : List.{1} Nat :=
  List.cons.{1} Nat 1
    (List.cons.{1} Nat 2
      (List.nil.{1} Nat))

def head_of_my_list : Nat :=
  match my_list : Nat with
  | List.nil => 0
  | List.cons a t => a

theorem head_eq_1 : Eq.{1} Nat head_of_my_list 1 :=
  Eq.refl.{1} Nat 1
