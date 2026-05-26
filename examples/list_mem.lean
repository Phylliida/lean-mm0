-- List membership predicate + decidability.
-- `List.mem a xs` is the canonical "a appears in xs" predicate,
-- defined by recursion on xs into `Or (Eq a h) (List.mem a t)`.
-- Decidability lifts via instDecidableOr from a user-supplied
-- decidable-equality function on α.

def List.mem.{u} {α : Sort u} (a : α) (xs : List.{u} α) : Prop :=
  match xs : Prop with
  | List.nil       => False
  | List.cons h t  => Or (Eq.{u} α a h) (List.mem a t)

example : List.mem 2 (List.cons.{1} Nat 1
                       (List.cons.{1} Nat 2
                         (List.cons.{1} Nat 3 (List.nil.{1} Nat)))) :=
  Or.inr (Eq.{1} Nat 2 1)
    (List.mem 2 (List.cons.{1} Nat 2
                  (List.cons.{1} Nat 3 (List.nil.{1} Nat))))
    (Or.inl (Eq.{1} Nat 2 2)
       (List.mem 2 (List.cons.{1} Nat 3 (List.nil.{1} Nat)))
       (Eq.refl.{1} Nat 2))

-- Decidable membership.  Takes a decEq function as a user-passed
-- argument (we don't have a DecidableEq class yet — but a class
-- version would just wrap this).  Compose isFalse for nil, and
-- instDecidableOr (decEq a h) (decMem a t) for cons.
def List.decMem.{u} {α : Sort u}
    (eq_dec : (a : α) -> (b : α) -> Decidable (Eq.{u} α a b))
    (a : α) (xs : List.{u} α) : Decidable (@List.mem.{u} α a xs) :=
  match (motive :=
           fun (ys : List.{u} α) =>
             Decidable (@List.mem.{u} α a ys)) xs with
  | List.nil =>
    Decidable.isFalse (@List.mem.{u} α a (List.nil.{u} α))
      (fun (h : False) => h)
  | List.cons h t =>
    @instDecidableOr (Eq.{u} α a h) (@List.mem.{u} α a t)
      (eq_dec a h) (List.decMem eq_dec a t)

-- Sanity: use decMem with Nat.decEq, dispatch via if.
def my_list : List.{1} Nat :=
  List.cons.{1} Nat 1
    (List.cons.{1} Nat 2
      (List.cons.{1} Nat 3 (List.nil.{1} Nat)))

example : Eq.{1} Nat
    (@ite.{1} Nat (List.mem 2 my_list)
       (List.decMem Nat.decEq 2 my_list) 99 0) 99 := by rfl

example : Eq.{1} Nat
    (@ite.{1} Nat (List.mem 5 my_list)
       (List.decMem Nat.decEq 5 my_list) 99 0) 0 := by rfl
