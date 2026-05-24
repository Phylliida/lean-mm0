-- Demonstrate universe-level inference: the user writes NO `.{u}`
-- annotations.  The elaborator fills both `α` and `u` from context.

def id_poly.{u} {α : Sort u} (x : α) : α := x

-- No .{1}, no Nat, no nothing — just `id_poly 3`.
def auto_id_three : Nat := id_poly 3

theorem auto_id_3_eq : Eq.{1} Nat auto_id_three 3 :=
  Eq.refl.{1} Nat 3

def const_fn.{u, v} {α : Sort u} {β : Sort v} (a : α) (b : β) : α := a

def auto_const : Nat := const_fn 7 Bool.true

theorem auto_const_eq : Eq.{1} Nat auto_const 7 :=
  Eq.refl.{1} Nat 7

-- The implicit and the level both come from context.
def compose3.{u, v, w}
    {α : Sort u} {β : Sort v} {γ : Sort w}
    (g : β -> γ) (f : α -> β) (x : α) : γ := g (f x)

def succ_then_succ : Nat := compose3 Nat.succ Nat.succ 5

theorem succ_then_succ_eq : Eq.{1} Nat succ_then_succ 7 :=
  Eq.refl.{1} Nat 7
