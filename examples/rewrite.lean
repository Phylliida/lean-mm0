-- `rewrite h` tactic.  When h : Eq α a b, replaces every occurrence of
-- `a` in the goal with `b` and leaves the rewritten goal as a subgoal.
-- Internally: builds an Eq.rec application with motive abstracting `a`.

-- Simplest case: rewrite + rfl finishes a trivial chain.
example : Eq.{1} Nat 3 3 :=
  by apply @Eq.trans.{1} Nat 3 3 3; rfl; rfl

-- Use rewrite to swap one side of an equality.
def rewrite_swap.{u} {α : Sort u} (a b : α) (h : Eq.{u} α a b) :
    Eq.{u} α b a :=
  by rewrite h; apply Eq.refl

-- Rewrite a complex term (multiple positions of `a` get replaced).
def rewrite_double.{u} {α : Sort u} (a b : α) (h : Eq.{u} α a b) :
    Eq.{u} (Prod.{u, u} α α) (Prod.mk.{u, u} α α a a) (Prod.mk.{u, u} α α b b) :=
  by rewrite h; apply Eq.refl

example : Eq.{1} Nat 5 5 :=
  rewrite_swap 5 5 (Eq.refl.{1} Nat 5)
