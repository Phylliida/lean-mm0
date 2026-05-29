-- Multi-rewrite: `rw [h1, h2, …]` chains rewrites, each operating
-- on the previous's residual subgoal.  Equivalent to writing
-- `rw h1; rw h2; …` but without the intermediate seq plumbing.

-- ============================================================
-- Transitivity via chained rewrites.  h1 : a = b, h2 : b = c.
-- Goal Eq α a c.  Rewrite by h1 (a → b), then by h2 (b → c),
-- giving Eq α c c.  Close with rfl.
-- ============================================================

theorem trans_via_rw.{u} {α : Sort u} (a : α) (b : α) (c : α)
    (h1 : Eq.{u} α a b) (h2 : Eq.{u} α b c) : Eq.{u} α a c :=
  by rw [h1, h2];
     apply Eq.refl

-- Sanity:
example : Eq.{1} Nat 3 3 :=
  trans_via_rw 3 3 3 (Eq.refl.{1} Nat 3) (Eq.refl.{1} Nat 3)

-- ============================================================
-- Single-rewrite form still works (backward compat).
-- ============================================================

theorem single_rw_still_works.{u} {α : Sort u} (a : α) (b : α)
    (h : Eq.{u} α a b) : Eq.{u} α a b :=
  by rw h;
     apply Eq.refl

-- ============================================================
-- Three-step chain: longer demo.  h1 : a = b, h2 : b = c,
-- h3 : c = d.  Goal Eq α a d.  After `rw [h1, h2, h3]`: Eq α d d.
-- ============================================================

theorem four_chain.{u} {α : Sort u} (a : α) (b : α) (c : α) (d : α)
    (h1 : Eq.{u} α a b) (h2 : Eq.{u} α b c) (h3 : Eq.{u} α c d) :
    Eq.{u} α a d :=
  by rw [h1, h2, h3];
     apply Eq.refl

example : Eq.{1} Nat 7 7 :=
  four_chain 7 7 7 7
    (Eq.refl.{1} Nat 7) (Eq.refl.{1} Nat 7) (Eq.refl.{1} Nat 7)
