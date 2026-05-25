-- Decidable equality on `List Nat`, building on Nat.decEq from
-- nat_dec_eq.lean.  Specialised to Nat for simplicity; the polymorphic
-- version would parameterise over `(α : Sort u)` plus a decidable
-- equality on α.  Same shape as Nat.decEq: use List.rec with motive
-- `fun xs => Π ys, Decidable (Eq xs ys)` so the IH is a function we
-- can apply to any new ys.

-- ============================================================
-- No-confusion: a predicate that's True at nil and False at any
-- cons.  Used to transport `Eq nil (cons _ _)` to False.
-- ============================================================

def list_nat_no_confuse (xs : List.{1} Nat) : Prop :=
  @List.rec.{1, 1} Nat
    (fun (_ : List.{1} Nat) => Prop)
    True
    (fun (_ : Nat) (_ : List.{1} Nat) (_ : Prop) => False)
    xs

example : Eq.{1} Prop (list_nat_no_confuse (List.nil.{1} Nat)) True :=
  Eq.refl.{1} Prop True

example :
    Eq.{1} Prop
      (list_nat_no_confuse (List.cons.{1} Nat 3 (List.nil.{1} Nat)))
      False :=
  Eq.refl.{1} Prop False

-- cons _ _ ≠ nil.
theorem cons_ne_nil_nat (a : Nat) (as : List.{1} Nat)
    (h : Eq.{1} (List.{1} Nat) (List.cons.{1} Nat a as) (List.nil.{1} Nat)) :
    False :=
  @Eq.rec.{1, 0} (List.{1} Nat) (List.nil.{1} Nat)
    (fun (k : List.{1} Nat)
         (_ : Eq.{1} (List.{1} Nat) (List.nil.{1} Nat) k) =>
       list_nat_no_confuse k)
    True.intro
    (List.cons.{1} Nat a as)
    (@Eq.symm.{1} (List.{1} Nat)
      (List.cons.{1} Nat a as) (List.nil.{1} Nat) h)

-- nil ≠ cons _ _.  Symmetric: just flip the equation.
theorem nil_ne_cons_nat (a : Nat) (as : List.{1} Nat)
    (h : Eq.{1} (List.{1} Nat) (List.nil.{1} Nat) (List.cons.{1} Nat a as)) :
    False :=
  cons_ne_nil_nat a as
    (@Eq.symm.{1} (List.{1} Nat)
      (List.nil.{1} Nat) (List.cons.{1} Nat a as) h)

-- ============================================================
-- Projections that read the head / tail with a default for nil.
-- Used in the injection lemmas to transport equalities through
-- Eq.rec with a motive that names the head / tail of the lhs.
-- ============================================================

def list_nat_head_or (default : Nat) (xs : List.{1} Nat) : Nat :=
  @List.rec.{1, 1} Nat
    (fun (_ : List.{1} Nat) => Nat)
    default
    (fun (a : Nat) (_ : List.{1} Nat) (_ : Nat) => a)
    xs

def list_nat_tail_or (default : List.{1} Nat) (xs : List.{1} Nat) :
    List.{1} Nat :=
  @List.rec.{1, 1} Nat
    (fun (_ : List.{1} Nat) => List.{1} Nat)
    default
    (fun (_ : Nat) (t : List.{1} Nat) (_ : List.{1} Nat) => t)
    xs

example : Eq.{1} Nat
    (list_nat_head_or 99 (List.cons.{1} Nat 7 (List.nil.{1} Nat))) 7 :=
  Eq.refl.{1} Nat 7
example : Eq.{1} Nat (list_nat_head_or 99 (List.nil.{1} Nat)) 99 :=
  Eq.refl.{1} Nat 99

-- ============================================================
-- Constructor injection: `cons a as = cons b bs` implies a = b
-- and as = bs.
-- ============================================================

theorem cons_inj_head_nat (a b : Nat) (as bs : List.{1} Nat)
    (h : Eq.{1} (List.{1} Nat)
                (List.cons.{1} Nat a as) (List.cons.{1} Nat b bs)) :
    Eq.{1} Nat a b :=
  @Eq.rec.{1, 0} (List.{1} Nat) (List.cons.{1} Nat a as)
    (fun (k : List.{1} Nat)
         (_ : Eq.{1} (List.{1} Nat) (List.cons.{1} Nat a as) k) =>
       Eq.{1} Nat a (list_nat_head_or a k))
    (Eq.refl.{1} Nat a)
    (List.cons.{1} Nat b bs) h

theorem cons_inj_tail_nat (a b : Nat) (as bs : List.{1} Nat)
    (h : Eq.{1} (List.{1} Nat)
                (List.cons.{1} Nat a as) (List.cons.{1} Nat b bs)) :
    Eq.{1} (List.{1} Nat) as bs :=
  @Eq.rec.{1, 0} (List.{1} Nat) (List.cons.{1} Nat a as)
    (fun (k : List.{1} Nat)
         (_ : Eq.{1} (List.{1} Nat) (List.cons.{1} Nat a as) k) =>
       Eq.{1} (List.{1} Nat) as (list_nat_tail_or as k))
    (Eq.refl.{1} (List.{1} Nat) as)
    (List.cons.{1} Nat b bs) h

-- Lift cons over equalities on the head AND tail: a = b ∧ as = bs
-- implies cons a as = cons b bs.  Used in the isTrue branch.
theorem cons_eq_intro (a b : Nat) (as bs : List.{1} Nat)
    (hh : Eq.{1} Nat a b)
    (ht : Eq.{1} (List.{1} Nat) as bs) :
    Eq.{1} (List.{1} Nat) (List.cons.{1} Nat a as) (List.cons.{1} Nat b bs) :=
  -- Rewrite a → b in `cons a as`, then as → bs.
  @Eq.rec.{1, 0} Nat a
    (fun (x : Nat) (_ : Eq.{1} Nat a x) =>
       Eq.{1} (List.{1} Nat)
              (List.cons.{1} Nat a as) (List.cons.{1} Nat x bs))
    -- After rewriting a → a, this is cons a as = cons a bs; lift via ht.
    (@Eq.rec.{1, 0} (List.{1} Nat) as
      (fun (xs : List.{1} Nat) (_ : Eq.{1} (List.{1} Nat) as xs) =>
         Eq.{1} (List.{1} Nat)
                (List.cons.{1} Nat a as) (List.cons.{1} Nat a xs))
      (Eq.refl.{1} (List.{1} Nat) (List.cons.{1} Nat a as))
      bs ht)
    b hh

-- ============================================================
-- List.decEq for List Nat.  Recursion on xs with motive
-- `fun xs => Π ys, Decidable (Eq xs ys)` so the IH is a function
-- applicable to any tail at the recursive step.
-- ============================================================

def List.decEq_nat (xs : List.{1} Nat) :
    (ys : List.{1} Nat) -> Decidable (Eq.{1} (List.{1} Nat) xs ys) :=
  @List.rec.{1, 1} Nat
    (fun (x : List.{1} Nat) =>
       (ys : List.{1} Nat) -> Decidable (Eq.{1} (List.{1} Nat) x ys))
    -- nil case: Π ys, Decidable (Eq nil ys)
    (fun (ys : List.{1} Nat) =>
      match (motive := fun (y : List.{1} Nat) =>
               Decidable (Eq.{1} (List.{1} Nat) (List.nil.{1} Nat) y)) ys with
      | List.nil =>
        Decidable.isTrue (Eq.{1} (List.{1} Nat)
          (List.nil.{1} Nat) (List.nil.{1} Nat))
          (Eq.refl.{1} (List.{1} Nat) (List.nil.{1} Nat))
      | List.cons b bs =>
        Decidable.isFalse (Eq.{1} (List.{1} Nat)
          (List.nil.{1} Nat) (List.cons.{1} Nat b bs))
          (nil_ne_cons_nat b bs))
    -- cons case: IH : Π ys, Decidable (Eq as ys); produce Π ys, Decidable (Eq (cons a as) ys)
    (fun (a : Nat) (as : List.{1} Nat)
         (ih : (ys : List.{1} Nat) ->
                 Decidable (Eq.{1} (List.{1} Nat) as ys)) =>
      fun (ys : List.{1} Nat) =>
        match (motive := fun (y : List.{1} Nat) =>
                 Decidable (Eq.{1} (List.{1} Nat)
                   (List.cons.{1} Nat a as) y)) ys with
        | List.nil =>
          Decidable.isFalse (Eq.{1} (List.{1} Nat)
            (List.cons.{1} Nat a as) (List.nil.{1} Nat))
            (cons_ne_nil_nat a as)
        | List.cons b bs =>
          -- Combine Decidable (a = b) with Decidable (as = bs)
          -- via two Decidable.rec splits.
          @Decidable.rec.{1} (Eq.{1} Nat a b)
            (fun (_ : Decidable (Eq.{1} Nat a b)) =>
               Decidable (Eq.{1} (List.{1} Nat)
                 (List.cons.{1} Nat a as) (List.cons.{1} Nat b bs)))
            -- head-neq branch: easy false
            (fun (h_neg : Not (Eq.{1} Nat a b)) =>
              Decidable.isFalse (Eq.{1} (List.{1} Nat)
                (List.cons.{1} Nat a as) (List.cons.{1} Nat b bs))
                (fun (h_eq : Eq.{1} (List.{1} Nat)
                  (List.cons.{1} Nat a as) (List.cons.{1} Nat b bs)) =>
                  h_neg (cons_inj_head_nat a b as bs h_eq)))
            -- head-eq branch: case on Decidable (as = bs)
            (fun (h_pos_head : Eq.{1} Nat a b) =>
              @Decidable.rec.{1} (Eq.{1} (List.{1} Nat) as bs)
                (fun (_ : Decidable (Eq.{1} (List.{1} Nat) as bs)) =>
                   Decidable (Eq.{1} (List.{1} Nat)
                     (List.cons.{1} Nat a as) (List.cons.{1} Nat b bs)))
                (fun (h_neg_tail : Not (Eq.{1} (List.{1} Nat) as bs)) =>
                  Decidable.isFalse (Eq.{1} (List.{1} Nat)
                    (List.cons.{1} Nat a as) (List.cons.{1} Nat b bs))
                    (fun (h_eq : Eq.{1} (List.{1} Nat)
                      (List.cons.{1} Nat a as) (List.cons.{1} Nat b bs)) =>
                      h_neg_tail (cons_inj_tail_nat a b as bs h_eq)))
                (fun (h_pos_tail : Eq.{1} (List.{1} Nat) as bs) =>
                  Decidable.isTrue (Eq.{1} (List.{1} Nat)
                    (List.cons.{1} Nat a as) (List.cons.{1} Nat b bs))
                    (cons_eq_intro a b as bs h_pos_head h_pos_tail))
                (ih bs))
            (Nat.decEq a b))
    xs

-- Sanity tests using ite to drive the decision.
example : Eq.{1} Nat
    (@ite.{1} Nat
      (Eq.{1} (List.{1} Nat)
        (List.cons.{1} Nat 1 (List.cons.{1} Nat 2 (List.nil.{1} Nat)))
        (List.cons.{1} Nat 1 (List.cons.{1} Nat 2 (List.nil.{1} Nat))))
      (List.decEq_nat
        (List.cons.{1} Nat 1 (List.cons.{1} Nat 2 (List.nil.{1} Nat)))
        (List.cons.{1} Nat 1 (List.cons.{1} Nat 2 (List.nil.{1} Nat))))
      42 0) 42 :=
  by rfl

example : Eq.{1} Nat
    (@ite.{1} Nat
      (Eq.{1} (List.{1} Nat)
        (List.cons.{1} Nat 1 (List.cons.{1} Nat 2 (List.nil.{1} Nat)))
        (List.cons.{1} Nat 1 (List.cons.{1} Nat 3 (List.nil.{1} Nat))))
      (List.decEq_nat
        (List.cons.{1} Nat 1 (List.cons.{1} Nat 2 (List.nil.{1} Nat)))
        (List.cons.{1} Nat 1 (List.cons.{1} Nat 3 (List.nil.{1} Nat))))
      42 0) 0 :=
  by rfl

example : Eq.{1} Nat
    (@ite.{1} Nat
      (Eq.{1} (List.{1} Nat)
        (List.nil.{1} Nat)
        (List.cons.{1} Nat 1 (List.nil.{1} Nat)))
      (List.decEq_nat
        (List.nil.{1} Nat)
        (List.cons.{1} Nat 1 (List.nil.{1} Nat)))
      42 0) 0 :=
  by rfl
