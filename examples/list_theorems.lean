-- Classical list theorems by induction.  Uses `length`, `map`,
-- `append` from list_ops.lean and `lift_succ` from nat_lemmas.lean.
--
-- All inductions go through the `induction` tactic; the polymorphic-
-- match-on-inner-Lam-binder fix from the previous iteration is what
-- makes the polymorphic statements parse correctly.

-- ============================================================
-- list_cons_lift: a = b → cons hd a = cons hd b.  A small congruence
-- lemma so the inductive proofs below stay readable.  Polymorphic.
-- ============================================================

theorem list_cons_lift.{u} {α : Sort u} (a : α) (xs ys : List.{u} α)
    (h : Eq.{u} (List.{u} α) xs ys) :
    Eq.{u} (List.{u} α)
      (@List.cons.{u} α a xs) (@List.cons.{u} α a ys) :=
  @Eq.rec.{u, 0} (List.{u} α) xs
    (fun (k : List.{u} α) (_ : Eq.{u} (List.{u} α) xs k) =>
       Eq.{u} (List.{u} α)
         (@List.cons.{u} α a xs) (@List.cons.{u} α a k))
    (Eq.refl.{u} (List.{u} α) (@List.cons.{u} α a xs))
    ys h

-- ============================================================
-- length_map: |map f xs| = |xs|.
-- Induction on xs:
--   nil: |map f nil| = |nil| = 0  (refl).
--   cons: |map f (cons a as)| = succ (|map f as|) = succ |as| (by ih)
--          = |cons a as|.  Reduces via lift_succ.
-- ============================================================

theorem length_map.{u, v} {α : Sort u} {β : Sort v}
    (f : α -> β) (xs : List.{u} α) :
    Eq.{1} Nat
      (@length.{v} β (@map.{u, v} α β f xs))
      (@length.{u} α xs) :=
  by induction xs;
     apply Eq.refl;
     intro a; intro as; intro ih;
     apply lift_succ;
     exact ih

example : Eq.{1} Nat
    (@length.{1} Nat
      (@map.{1, 1} Nat Nat (fun (n : Nat) => Nat.mul n 2) my_nats)) 3 :=
  length_map.{1, 1} (fun (n : Nat) => Nat.mul n 2) my_nats

-- ============================================================
-- map_append: map f (xs ++ ys) = map f xs ++ map f ys.
-- Induction on xs:
--   nil: map f (nil ++ ys) = map f ys, RHS = map f nil ++ map f ys
--        = nil ++ map f ys = map f ys.  Refl.
--   cons: LHS = cons (f a) (map f (as ++ ys));
--         RHS = cons (f a) (map f as ++ map f ys).
--         Lift ih through `cons (f a) _` via list_cons_lift.
-- ============================================================

theorem map_append.{u, v} {α : Sort u} {β : Sort v}
    (f : α -> β) (xs ys : List.{u} α) :
    Eq.{v} (List.{v} β)
      (@map.{u, v} α β f (@append.{u} α xs ys))
      (@append.{v} β (@map.{u, v} α β f xs) (@map.{u, v} α β f ys)) :=
  by induction xs;
     apply Eq.refl;
     intro a; intro as; intro ih;
     apply (list_cons_lift.{v} (f a)
              (@map.{u, v} α β f (@append.{u} α as ys))
              (@append.{v} β (@map.{u, v} α β f as) (@map.{u, v} α β f ys)));
     exact ih

example : Eq.{1} (List.{1} Nat)
    (@map.{1, 1} Nat Nat (fun (n : Nat) => Nat.mul n 2)
      (@append.{1} Nat my_nats my_nats))
    (@append.{1} Nat
      (@map.{1, 1} Nat Nat (fun (n : Nat) => Nat.mul n 2) my_nats)
      (@map.{1, 1} Nat Nat (fun (n : Nat) => Nat.mul n 2) my_nats)) :=
  map_append.{1, 1} (fun (n : Nat) => Nat.mul n 2) my_nats my_nats

-- ============================================================
-- map_compose: map f (map g xs) = map (f ∘ g) xs.
-- We write `f ∘ g` inline as `fun x => f (g x)` since notation isn't
-- in scope.  Induction on xs:
--   nil: map f (map g nil) = map f nil = nil; map (f ∘ g) nil = nil.  Refl.
--   cons: LHS = map f (cons (g a) (map g as)) = cons (f (g a)) (map f (map g as));
--         RHS = cons ((f ∘ g) a) (map (f ∘ g) as) = cons (f (g a)) (map (f ∘ g) as).
--         Lift ih through `cons (f (g a)) _`.
-- ============================================================

theorem map_compose.{u, v, w}
    {α : Sort u} {β : Sort v} {γ : Sort w}
    (f : β -> γ) (g : α -> β) (xs : List.{u} α) :
    Eq.{w} (List.{w} γ)
      (@map.{v, w} β γ f (@map.{u, v} α β g xs))
      (@map.{u, w} α γ (fun (x : α) => f (g x)) xs) :=
  by induction xs;
     apply Eq.refl;
     intro a; intro as; intro ih;
     apply (list_cons_lift.{w} (f (g a))
              (@map.{v, w} β γ f (@map.{u, v} α β g as))
              (@map.{u, w} α γ (fun (x : α) => f (g x)) as));
     exact ih

example : Eq.{1} (List.{1} Nat)
    (@map.{1, 1} Nat Nat (fun (n : Nat) => Nat.succ n)
      (@map.{1, 1} Nat Nat (fun (n : Nat) => Nat.mul n 2) my_nats))
    (@map.{1, 1} Nat Nat (fun (x : Nat) =>
        Nat.succ (Nat.mul x 2)) my_nats) :=
  map_compose.{1, 1, 1}
    (fun (n : Nat) => Nat.succ n)
    (fun (n : Nat) => Nat.mul n 2)
    my_nats
