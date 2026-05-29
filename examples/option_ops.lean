-- Option type utilities.  `Option α` is in stdlib (Option.none /
-- Option.some).  This file adds the standard Functor-ish operations
-- (map, getD, bind, isSome, isNone) and a parametric DecidableEq
-- instance lifting from the element type.

-- ============================================================
-- map: Option α → Option β under a function f : α → β.
-- ============================================================

def Option.map.{u, v} {α : Sort u} {β : Sort v}
    (f : α -> β) (o : Option.{u} α) : Option.{v} β :=
  match (motive := fun (_ : Option.{u} α) => Option.{v} β) o with
  | Option.none   => Option.none.{v} β
  | Option.some x => Option.some.{v} β (f x)

example : Eq.{1} (Option.{1} Nat)
    (@Option.map.{1, 1} Nat Nat (fun (n : Nat) => Nat.succ n)
       (Option.some.{1} Nat 4))
    (Option.some.{1} Nat 5) := by rfl

example : Eq.{1} (Option.{1} Nat)
    (@Option.map.{1, 1} Nat Nat (fun (n : Nat) => Nat.succ n)
       (Option.none.{1} Nat))
    (Option.none.{1} Nat) := by rfl

-- ============================================================
-- getD (get-or-default): Option α → α → α.  Used to extract a value
-- with a fallback.
-- ============================================================

def Option.getD.{u} {α : Sort u} (o : Option.{u} α) (d : α) : α :=
  match (motive := fun (_ : Option.{u} α) => α) o with
  | Option.none   => d
  | Option.some x => x

example : Eq.{1} Nat (@Option.getD.{1} Nat (Option.some.{1} Nat 7) 0) 7 :=
  by rfl
example : Eq.{1} Nat (@Option.getD.{1} Nat (Option.none.{1} Nat) 42) 42 :=
  by rfl

-- ============================================================
-- bind: monadic compose for Option.
-- ============================================================

def Option.bind.{u, v} {α : Sort u} {β : Sort v}
    (o : Option.{u} α) (f : α -> Option.{v} β) : Option.{v} β :=
  match (motive := fun (_ : Option.{u} α) => Option.{v} β) o with
  | Option.none   => Option.none.{v} β
  | Option.some x => f x

example : Eq.{1} (Option.{1} Nat)
    (@Option.bind.{1, 1} Nat Nat
       (Option.some.{1} Nat 3)
       (fun (n : Nat) => Option.some.{1} Nat (Nat.succ n)))
    (Option.some.{1} Nat 4) := by rfl

-- ============================================================
-- isSome / isNone: Bool predicates.
-- ============================================================

def Option.isSome.{u} {α : Sort u} (o : Option.{u} α) : Bool :=
  match (motive := fun (_ : Option.{u} α) => Bool) o with
  | Option.none   => Bool.false
  | Option.some _ => Bool.true

def Option.isNone.{u} {α : Sort u} (o : Option.{u} α) : Bool :=
  match (motive := fun (_ : Option.{u} α) => Bool) o with
  | Option.none   => Bool.true
  | Option.some _ => Bool.false

example : Eq.{1} Bool (@Option.isSome.{1} Nat (Option.some.{1} Nat 3))
                      Bool.true := by rfl
example : Eq.{1} Bool (@Option.isNone.{1} Nat (Option.none.{1} Nat))
                      Bool.true := by rfl

-- ============================================================
-- No-confusion helpers for Option (mirrors list_no_confuse).
-- ============================================================

def option_no_confuse.{u} {α : Sort u} (o : Option.{u} α) : Prop :=
  @Option.rec.{u, 1} α
    (fun (_ : Option.{u} α) => Prop)
    True
    (fun (_ : α) => False)
    o

example : Eq.{1} Prop (@option_no_confuse.{1} Nat (Option.none.{1} Nat))
                      True := by rfl
example : Eq.{1} Prop
    (@option_no_confuse.{1} Nat (Option.some.{1} Nat 7)) False := by rfl

theorem some_ne_none.{u} {α : Sort u} (a : α)
    (h : Eq.{u} (Option.{u} α) (Option.some.{u} α a) (Option.none.{u} α)) :
    False :=
  @Eq.rec.{u, 0} (Option.{u} α) (Option.none.{u} α)
    (fun (k : Option.{u} α)
         (_ : Eq.{u} (Option.{u} α) (Option.none.{u} α) k) =>
       @option_no_confuse.{u} α k)
    True.intro
    (Option.some.{u} α a)
    (@Eq.symm.{u} (Option.{u} α)
      (Option.some.{u} α a) (Option.none.{u} α) h)

theorem none_ne_some.{u} {α : Sort u} (a : α)
    (h : Eq.{u} (Option.{u} α) (Option.none.{u} α) (Option.some.{u} α a)) :
    False :=
  some_ne_none.{u} a
    (@Eq.symm.{u} (Option.{u} α)
      (Option.none.{u} α) (Option.some.{u} α a) h)

-- some-injection: Option.some a = Option.some b → a = b.
def option_unwrap.{u} {α : Sort u} (d : α) (o : Option.{u} α) : α :=
  @Option.rec.{u, u} α
    (fun (_ : Option.{u} α) => α)
    d
    (fun (a : α) => a)
    o

theorem some_inj.{u} {α : Sort u} (a b : α)
    (h : Eq.{u} (Option.{u} α) (Option.some.{u} α a) (Option.some.{u} α b)) :
    Eq.{u} α a b :=
  @Eq.rec.{u, 0} (Option.{u} α) (Option.some.{u} α a)
    (fun (k : Option.{u} α)
         (_ : Eq.{u} (Option.{u} α) (Option.some.{u} α a) k) =>
       Eq.{u} α a (@option_unwrap.{u} α a k))
    (Eq.refl.{u} α a)
    (Option.some.{u} α b) h

-- ============================================================
-- Decidable equality on Option α, polymorphic over the element
-- decision function.  Two nested matches on x and y, then
-- Decidable.rec on the element-level decision for the some-some case.
-- ============================================================

def Option.decEq.{u} {α : Sort u}
    (αDecEq : (a : α) -> (b : α) -> Decidable (Eq.{u} α a b))
    (x : Option.{u} α) (y : Option.{u} α) :
    Decidable (Eq.{u} (Option.{u} α) x y) :=
  match (motive := fun (y1 : Option.{u} α) =>
           Decidable (Eq.{u} (Option.{u} α) x y1)) y with
  | Option.none =>
    (match (motive := fun (x1 : Option.{u} α) =>
             Decidable (Eq.{u} (Option.{u} α) x1 (Option.none.{u} α))) x with
    | Option.none =>
      Decidable.isTrue
        (Eq.{u} (Option.{u} α) (Option.none.{u} α) (Option.none.{u} α))
        (Eq.refl.{u} (Option.{u} α) (Option.none.{u} α))
    | Option.some a =>
      Decidable.isFalse
        (Eq.{u} (Option.{u} α) (Option.some.{u} α a) (Option.none.{u} α))
        (some_ne_none.{u} a))
  | Option.some b =>
    (match (motive := fun (x1 : Option.{u} α) =>
             Decidable (Eq.{u} (Option.{u} α) x1 (Option.some.{u} α b))) x with
    | Option.none =>
      Decidable.isFalse
        (Eq.{u} (Option.{u} α) (Option.none.{u} α) (Option.some.{u} α b))
        (none_ne_some.{u} b)
    | Option.some a =>
      @Decidable.rec.{1} (Eq.{u} α a b)
        (fun (_ : Decidable (Eq.{u} α a b)) =>
           Decidable (Eq.{u} (Option.{u} α)
             (Option.some.{u} α a) (Option.some.{u} α b)))
        (fun (h_neg : Not (Eq.{u} α a b)) =>
          Decidable.isFalse
            (Eq.{u} (Option.{u} α)
              (Option.some.{u} α a) (Option.some.{u} α b))
            (fun (h_eq : Eq.{u} (Option.{u} α)
                                (Option.some.{u} α a) (Option.some.{u} α b)) =>
              h_neg (some_inj.{u} a b h_eq)))
        (fun (h_pos : Eq.{u} α a b) =>
          Decidable.isTrue
            (Eq.{u} (Option.{u} α)
              (Option.some.{u} α a) (Option.some.{u} α b))
            (@Eq.rec.{u, 0} α a
              (fun (x : α) (_ : Eq.{u} α a x) =>
                 Eq.{u} (Option.{u} α)
                        (Option.some.{u} α a) (Option.some.{u} α x))
              (Eq.refl.{u} (Option.{u} α) (Option.some.{u} α a))
              b h_pos))
        (αDecEq a b))

-- Sanity: with Nat.decEq.
example : Eq.{1} Nat
    (@ite.{1} Nat
       (Eq.{1} (Option.{1} Nat) (Option.some.{1} Nat 3) (Option.some.{1} Nat 3))
       (Option.decEq.{1} Nat.decEq (Option.some.{1} Nat 3) (Option.some.{1} Nat 3))
       99 0)
    99 := by rfl

example : Eq.{1} Nat
    (@ite.{1} Nat
       (Eq.{1} (Option.{1} Nat) (Option.some.{1} Nat 3) (Option.some.{1} Nat 4))
       (Option.decEq.{1} Nat.decEq (Option.some.{1} Nat 3) (Option.some.{1} Nat 4))
       99 0)
    0 := by rfl

example : Eq.{1} Nat
    (@ite.{1} Nat
       (Eq.{1} (Option.{1} Nat) (Option.none.{1} Nat) (Option.none.{1} Nat))
       (Option.decEq.{1} Nat.decEq (Option.none.{1} Nat) (Option.none.{1} Nat))
       99 0)
    99 := by rfl
