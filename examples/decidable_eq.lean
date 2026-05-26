-- DecidableEq class: bundles the decision procedure for equality on α
-- as a typeclass.

class DecidableEq.{u} (α : Sort u) : Sort 1 where
  decEq : (a : α) -> (b : α) -> Decidable (Eq.{u} α a b)

instance instDecidableEqNat : DecidableEq.{1} Nat :=
  DecidableEq.mk.{1} Nat Nat.decEq

-- Sanity: synthesis finds the Nat instance and uses it.  Note we
-- write `DecidableEq.decEq 3 3` (α inferred from `3 : Nat`, instance
-- synthesised), not `DecidableEq.decEq.{1} Nat 3 3` (which would put
-- `Nat` in the explicit `a : α` slot — wrong, since α and the self
-- instance are implicit/inst-implicit).
example : Eq.{1} Nat
    (@ite.{1} Nat (Eq.{1} Nat 3 3)
       (DecidableEq.decEq 3 3) 99 0) 99 := by rfl

example : Eq.{1} Nat
    (@ite.{1} Nat (Eq.{1} Nat 3 4)
       (DecidableEq.decEq 3 4) 99 0) 0 := by rfl

-- Class-driven List.decMem: takes [DecidableEq α] instead of an
-- explicit eq_dec arg.  Body delegates to the underlying class
-- projection.
def List.decMem_cls.{u} {α : Sort u} [da : DecidableEq.{u} α]
    (a : α) (xs : List.{u} α) : Decidable (@List.mem.{u} α a xs) :=
  match (motive :=
           fun (ys : List.{u} α) =>
             Decidable (@List.mem.{u} α a ys)) xs with
  | List.nil =>
    Decidable.isFalse (@List.mem.{u} α a (List.nil.{u} α))
      (fun (h : False) => h)
  | List.cons h t =>
    @instDecidableOr (Eq.{u} α a h) (@List.mem.{u} α a t)
      (DecidableEq.decEq a h)
      (List.decMem_cls a t)

def my_list_3 : List.{1} Nat :=
  List.cons.{1} Nat 1
    (List.cons.{1} Nat 2
      (List.cons.{1} Nat 3 (List.nil.{1} Nat)))

example : Eq.{1} Nat
    (@ite.{1} Nat (List.mem 2 my_list_3)
       (List.decMem_cls 2 my_list_3) 99 0) 99 := by rfl

example : Eq.{1} Nat
    (@ite.{1} Nat (List.mem 5 my_list_3)
       (List.decMem_cls 5 my_list_3) 99 0) 0 := by rfl
