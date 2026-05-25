-- Polymorphic Decidable equality on List α: given an element-wise
-- decidable equality on α, derive one on List α.  Same shape as the
-- Nat-specialised version in list_dec_eq.lean, but with α a universe-
-- polymorphic parameter and the element equality passed explicitly.

-- ============================================================
-- No-confusion: True at nil, False at cons.
-- ============================================================

def list_no_confuse.{u} {α : Sort u} (xs : List.{u} α) : Prop :=
  @List.rec.{u, 1} α
    (fun (_ : List.{u} α) => Prop)
    True
    (fun (_ : α) (_ : List.{u} α) (_ : Prop) => False)
    xs

example : Eq.{1} Prop (list_no_confuse.{1} (List.nil.{1} Nat)) True :=
  Eq.refl.{1} Prop True
example :
    Eq.{1} Prop
      (list_no_confuse.{1} (List.cons.{1} Nat 0 (List.nil.{1} Nat)))
      False :=
  Eq.refl.{1} Prop False

-- ============================================================
-- cons ≠ nil and nil ≠ cons.
-- ============================================================

theorem cons_ne_nil.{u} {α : Sort u} (a : α) (as : List.{u} α)
    (h : Eq.{u} (List.{u} α) (List.cons.{u} α a as) (List.nil.{u} α)) :
    False :=
  @Eq.rec.{u, 0} (List.{u} α) (List.nil.{u} α)
    (fun (k : List.{u} α) (_ : Eq.{u} (List.{u} α) (List.nil.{u} α) k) =>
       list_no_confuse.{u} k)
    True.intro
    (List.cons.{u} α a as)
    (@Eq.symm.{u} (List.{u} α)
      (List.cons.{u} α a as) (List.nil.{u} α) h)

theorem nil_ne_cons.{u} {α : Sort u} (a : α) (as : List.{u} α)
    (h : Eq.{u} (List.{u} α) (List.nil.{u} α) (List.cons.{u} α a as)) :
    False :=
  cons_ne_nil.{u} a as
    (@Eq.symm.{u} (List.{u} α)
      (List.nil.{u} α) (List.cons.{u} α a as) h)

-- ============================================================
-- Head / tail with a nil default.
-- ============================================================

def list_head_or.{u} {α : Sort u} (default : α) (xs : List.{u} α) : α :=
  @List.rec.{u, u} α
    (fun (_ : List.{u} α) => α)
    default
    (fun (a : α) (_ : List.{u} α) (_ : α) => a)
    xs

def list_tail_or.{u} {α : Sort u} (default : List.{u} α) (xs : List.{u} α) :
    List.{u} α :=
  @List.rec.{u, u} α
    (fun (_ : List.{u} α) => List.{u} α)
    default
    (fun (_ : α) (t : List.{u} α) (_ : List.{u} α) => t)
    xs

-- ============================================================
-- Constructor injection.
-- ============================================================

theorem cons_inj_head.{u} {α : Sort u} (a b : α) (as bs : List.{u} α)
    (h : Eq.{u} (List.{u} α)
                (List.cons.{u} α a as) (List.cons.{u} α b bs)) :
    Eq.{u} α a b :=
  @Eq.rec.{u, 0} (List.{u} α) (List.cons.{u} α a as)
    (fun (k : List.{u} α)
         (_ : Eq.{u} (List.{u} α) (List.cons.{u} α a as) k) =>
       Eq.{u} α a (list_head_or.{u} a k))
    (Eq.refl.{u} α a)
    (List.cons.{u} α b bs) h

theorem cons_inj_tail.{u} {α : Sort u} (a b : α) (as bs : List.{u} α)
    (h : Eq.{u} (List.{u} α)
                (List.cons.{u} α a as) (List.cons.{u} α b bs)) :
    Eq.{u} (List.{u} α) as bs :=
  @Eq.rec.{u, 0} (List.{u} α) (List.cons.{u} α a as)
    (fun (k : List.{u} α)
         (_ : Eq.{u} (List.{u} α) (List.cons.{u} α a as) k) =>
       Eq.{u} (List.{u} α) as (list_tail_or.{u} as k))
    (Eq.refl.{u} (List.{u} α) as)
    (List.cons.{u} α b bs) h

theorem cons_eq_intro.{u} {α : Sort u} (a b : α) (as bs : List.{u} α)
    (hh : Eq.{u} α a b)
    (ht : Eq.{u} (List.{u} α) as bs) :
    Eq.{u} (List.{u} α) (List.cons.{u} α a as) (List.cons.{u} α b bs) :=
  @Eq.rec.{u, 0} α a
    (fun (x : α) (_ : Eq.{u} α a x) =>
       Eq.{u} (List.{u} α)
              (List.cons.{u} α a as) (List.cons.{u} α x bs))
    (@Eq.rec.{u, 0} (List.{u} α) as
      (fun (xs : List.{u} α) (_ : Eq.{u} (List.{u} α) as xs) =>
         Eq.{u} (List.{u} α)
                (List.cons.{u} α a as) (List.cons.{u} α a xs))
      (Eq.refl.{u} (List.{u} α) (List.cons.{u} α a as))
      bs ht)
    b hh

-- ============================================================
-- List.decEq, polymorphic.  Takes the element decEq explicitly
-- (no typeclass machinery needed — typeclasses are an organisation
-- of the same thing).
-- ============================================================

def List.decEq.{u} {α : Sort u}
    (αDecEq : (a : α) -> (b : α) -> Decidable (Eq.{u} α a b))
    (xs : List.{u} α) :
    (ys : List.{u} α) -> Decidable (Eq.{u} (List.{u} α) xs ys) :=
  @List.rec.{u, imax u 1} α
    (fun (x : List.{u} α) =>
       (ys : List.{u} α) -> Decidable (Eq.{u} (List.{u} α) x ys))
    -- nil case
    (fun (ys : List.{u} α) =>
      match (motive := fun (y : List.{u} α) =>
               Decidable (Eq.{u} (List.{u} α) (List.nil.{u} α) y)) ys with
      | List.nil =>
        Decidable.isTrue (Eq.{u} (List.{u} α)
          (List.nil.{u} α) (List.nil.{u} α))
          (Eq.refl.{u} (List.{u} α) (List.nil.{u} α))
      | List.cons b bs =>
        Decidable.isFalse (Eq.{u} (List.{u} α)
          (List.nil.{u} α) (List.cons.{u} α b bs))
          (nil_ne_cons.{u} b bs))
    -- cons case
    (fun (a : α) (as : List.{u} α)
         (ih : (ys : List.{u} α) ->
                 Decidable (Eq.{u} (List.{u} α) as ys)) =>
      fun (ys : List.{u} α) =>
        match (motive := fun (y : List.{u} α) =>
                 Decidable (Eq.{u} (List.{u} α)
                   (List.cons.{u} α a as) y)) ys with
        | List.nil =>
          Decidable.isFalse (Eq.{u} (List.{u} α)
            (List.cons.{u} α a as) (List.nil.{u} α))
            (cons_ne_nil.{u} a as)
        | List.cons b bs =>
          @Decidable.rec.{1} (Eq.{u} α a b)
            (fun (_ : Decidable (Eq.{u} α a b)) =>
               Decidable (Eq.{u} (List.{u} α)
                 (List.cons.{u} α a as) (List.cons.{u} α b bs)))
            (fun (h_neg : Not (Eq.{u} α a b)) =>
              Decidable.isFalse (Eq.{u} (List.{u} α)
                (List.cons.{u} α a as) (List.cons.{u} α b bs))
                (fun (h_eq : Eq.{u} (List.{u} α)
                  (List.cons.{u} α a as) (List.cons.{u} α b bs)) =>
                  h_neg (cons_inj_head.{u} a b as bs h_eq)))
            (fun (h_pos_head : Eq.{u} α a b) =>
              @Decidable.rec.{1} (Eq.{u} (List.{u} α) as bs)
                (fun (_ : Decidable (Eq.{u} (List.{u} α) as bs)) =>
                   Decidable (Eq.{u} (List.{u} α)
                     (List.cons.{u} α a as) (List.cons.{u} α b bs)))
                (fun (h_neg_tail : Not (Eq.{u} (List.{u} α) as bs)) =>
                  Decidable.isFalse (Eq.{u} (List.{u} α)
                    (List.cons.{u} α a as) (List.cons.{u} α b bs))
                    (fun (h_eq : Eq.{u} (List.{u} α)
                      (List.cons.{u} α a as) (List.cons.{u} α b bs)) =>
                      h_neg_tail (cons_inj_tail.{u} a b as bs h_eq)))
                (fun (h_pos_tail : Eq.{u} (List.{u} α) as bs) =>
                  Decidable.isTrue (Eq.{u} (List.{u} α)
                    (List.cons.{u} α a as) (List.cons.{u} α b bs))
                    (cons_eq_intro.{u} a b as bs h_pos_head h_pos_tail))
                (ih bs))
            (αDecEq a b))
    xs

-- ============================================================
-- Use it: instantiate at α = Nat with Nat.decEq.  Same sanity
-- tests as list_dec_eq.lean.
-- ============================================================

example : Eq.{1} Nat
    (@ite.{1} Nat
      (Eq.{1} (List.{1} Nat)
        (List.cons.{1} Nat 1 (List.cons.{1} Nat 2 (List.nil.{1} Nat)))
        (List.cons.{1} Nat 1 (List.cons.{1} Nat 2 (List.nil.{1} Nat))))
      (List.decEq.{1} Nat.decEq
        (List.cons.{1} Nat 1 (List.cons.{1} Nat 2 (List.nil.{1} Nat)))
        (List.cons.{1} Nat 1 (List.cons.{1} Nat 2 (List.nil.{1} Nat))))
      42 0) 42 :=
  by rfl

example : Eq.{1} Nat
    (@ite.{1} Nat
      (Eq.{1} (List.{1} Nat)
        (List.cons.{1} Nat 1 (List.cons.{1} Nat 2 (List.nil.{1} Nat)))
        (List.cons.{1} Nat 1 (List.cons.{1} Nat 3 (List.nil.{1} Nat))))
      (List.decEq.{1} Nat.decEq
        (List.cons.{1} Nat 1 (List.cons.{1} Nat 2 (List.nil.{1} Nat)))
        (List.cons.{1} Nat 1 (List.cons.{1} Nat 3 (List.nil.{1} Nat))))
      42 0) 0 :=
  by rfl
