-- Compositional Decidable instances: from Decidable p / Decidable q
-- build Decidable (And p q), Decidable (Or p q), Decidable (Not p).
--
-- Each is registered as an `instance` so it participates in synthesis.

-- ---- Helpers: project from And, eliminate Or, etc. (no projections
-- ---- are auto-generated for raw inductives like And, so we use And.rec.)

def And.left (p q : Prop) (h : And p q) : p :=
  @And.rec p q (fun (_ : And p q) => p) (fun (hp : p) (_ : q) => hp) h

def And.right (p q : Prop) (h : And p q) : q :=
  @And.rec p q (fun (_ : And p q) => q) (fun (_ : p) (hq : q) => hq) h

def Or.elim (p q : Prop) (r : Prop) (h : Or p q) (hp_r : p -> r) (hq_r : q -> r) : r :=
  @Or.rec p q (fun (_ : Or p q) => r) hp_r hq_r h

-- ---- Decidable (And p q)

instance instDecidableAnd {p q : Prop} [dp : Decidable p] [dq : Decidable q] :
    Decidable (And p q) :=
  match dp : Decidable (And p q) with
  | Decidable.isFalse hp =>
    Decidable.isFalse (And p q) (fun (h : And p q) => hp (And.left p q h))
  | Decidable.isTrue hp =>
    match dq : Decidable (And p q) with
    | Decidable.isFalse hq =>
      Decidable.isFalse (And p q) (fun (h : And p q) => hq (And.right p q h))
    | Decidable.isTrue hq =>
      Decidable.isTrue (And p q) (And.intro p q hp hq)

-- ---- Decidable (Or p q)

instance instDecidableOr {p q : Prop} [dp : Decidable p] [dq : Decidable q] :
    Decidable (Or p q) :=
  match dp : Decidable (Or p q) with
  | Decidable.isTrue hp =>
    Decidable.isTrue (Or p q) (Or.inl p q hp)
  | Decidable.isFalse hp =>
    match dq : Decidable (Or p q) with
    | Decidable.isTrue hq =>
      Decidable.isTrue (Or p q) (Or.inr p q hq)
    | Decidable.isFalse hq =>
      Decidable.isFalse (Or p q) (fun (h : Or p q) =>
        Or.elim p q False h hp hq)

-- ---- Decidable (Not p)

instance instDecidableNot {p : Prop} [dp : Decidable p] : Decidable (Not p) :=
  match dp : Decidable (Not p) with
  | Decidable.isTrue hp =>
    Decidable.isFalse (Not p) (fun (np : Not p) => np hp)
  | Decidable.isFalse hp =>
    Decidable.isTrue (Not p) hp

-- ---- Sanity checks: synthesis composes through these.

example : Eq.{1} Nat (if (And True True) then 1 else 2) 1 := by rfl
example : Eq.{1} Nat (if (And True False) then 1 else 2) 2 := by rfl
example : Eq.{1} Nat (if (Or False True) then 1 else 2) 1 := by rfl
example : Eq.{1} Nat (if (Or False False) then 1 else 2) 2 := by rfl
example : Eq.{1} Nat (if (Not True) then 1 else 2) 2 := by rfl
example : Eq.{1} Nat (if (Not False) then 1 else 2) 1 := by rfl
example : Eq.{1} Nat (if (And True (Not False)) then 1 else 2) 1 := by rfl
