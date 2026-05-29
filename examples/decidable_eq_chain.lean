-- Chain DecidableEq through more types.  Bool gets a direct
-- instance via Bool.decEq; List α gets a parametric instance over
-- `[DecidableEq α]` so synthesis lifts Nat / Bool decidability up
-- to lists of them automatically.

-- ============================================================
-- DecidableEq Bool.
-- ============================================================

instance instDecidableEqBool : DecidableEq.{1} Bool :=
  DecidableEq.mk.{1} Bool Bool.decEq

example : Eq.{1} Nat
    (@ite.{1} Nat (Eq.{1} Bool Bool.true Bool.true)
       (DecidableEq.decEq Bool.true Bool.true) 99 0) 99 := by rfl

example : Eq.{1} Nat
    (@ite.{1} Nat (Eq.{1} Bool Bool.true Bool.false)
       (DecidableEq.decEq Bool.true Bool.false) 99 0) 0 := by rfl

-- ============================================================
-- DecidableEq α → DecidableEq (List α), parametric.  Synthesis
-- will assemble this from the available element instances.
-- ============================================================

instance instDecidableEqList.{u} {α : Sort u} [da : DecidableEq.{u} α] :
    DecidableEq.{u} (List.{u} α) :=
  DecidableEq.mk.{u} (List.{u} α)
    (fun (xs : List.{u} α) (ys : List.{u} α) =>
      List.decEq.{u} (@DecidableEq.decEq.{u} α da) xs ys)

-- Synthesis finds instDecidableEqList ∘ instDecidableEqNat.
def some_nat_list : List.{1} Nat :=
  List.cons.{1} Nat 1
    (List.cons.{1} Nat 2 (List.cons.{1} Nat 3 (List.nil.{1} Nat)))

def same_nat_list : List.{1} Nat :=
  List.cons.{1} Nat 1
    (List.cons.{1} Nat 2 (List.cons.{1} Nat 3 (List.nil.{1} Nat)))

def diff_nat_list : List.{1} Nat :=
  List.cons.{1} Nat 1
    (List.cons.{1} Nat 2 (List.cons.{1} Nat 4 (List.nil.{1} Nat)))

example : Eq.{1} Nat
    (@ite.{1} Nat (Eq.{1} (List.{1} Nat) some_nat_list same_nat_list)
       (DecidableEq.decEq some_nat_list same_nat_list) 42 0) 42 :=
  by rfl

example : Eq.{1} Nat
    (@ite.{1} Nat (Eq.{1} (List.{1} Nat) some_nat_list diff_nat_list)
       (DecidableEq.decEq some_nat_list diff_nat_list) 42 0) 0 :=
  by rfl

-- And with List Bool: synthesis assembles instDecidableEqList ∘
-- instDecidableEqBool.
def some_bool_list : List.{1} Bool :=
  List.cons.{1} Bool Bool.true
    (List.cons.{1} Bool Bool.false (List.nil.{1} Bool))

def same_bool_list : List.{1} Bool :=
  List.cons.{1} Bool Bool.true
    (List.cons.{1} Bool Bool.false (List.nil.{1} Bool))

example : Eq.{1} Nat
    (@ite.{1} Nat (Eq.{1} (List.{1} Bool) some_bool_list same_bool_list)
       (DecidableEq.decEq some_bool_list same_bool_list) 7 0) 7 :=
  by rfl
