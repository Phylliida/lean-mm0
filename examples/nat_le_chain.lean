-- More Nat.le ordering lemmas, exercising the new induction-with-
-- index-unification + auto-revert infrastructure to prove the
-- pred_le_pred → lt_irrefl chain.

-- ============================================================
-- Nat.pred_le_pred: succ n ≤ succ m → n ≤ m.
--
-- The canonical use of index unification.  Induct on h : Le (succ n)
-- (succ m).  Both indices are concrete, so the tactic introduces
-- k_new + h_eq : Eq Nat (succ m) k_new and abstracts.  In each
-- branch we use h_eq + succ_inj to derive an equation between m and
-- the branch's index, then transport refl through it (refl branch)
-- or use the IH-companion h_inner as a Nat.lt witness (step branch).
-- ============================================================

theorem Nat.pred_le_pred (n m : Nat)
    (h : Nat.le (Nat.succ n) (Nat.succ m)) : Nat.le n m :=
  by induction h;
     -- refl branch: minor = Π h_eq : Eq Nat (succ m) (succ n). Le n m.
     -- Derive m = n from h_eq via succ_inj, rewrite m → n in goal,
     -- close with Le.refl.
     intro h_eq;
     rewrite (succ_inj m n h_eq);
     apply Nat.le.refl;
     -- step branch: minor =
     --   Π m1 : Nat. Π h_inner : Le (succ n) m1. Π ih : ...
     --   Π h_eq : Eq Nat (succ m) (succ m1). Le n m.
     -- Derive m = m1 from h_eq, rewrite m → m1 in goal, then close
     -- with le_of_lt h_inner (since Lt n m1 = Le (succ n) m1 defly).
     intro m1; intro h_inner; intro ih; intro h_eq;
     rewrite (succ_inj m m1 h_eq);
     apply Nat.le_of_lt;
     exact h_inner

example : Nat.le 2 3 :=
  Nat.pred_le_pred 2 3
    (Nat.le.step 3 3 (Nat.le.refl 3))

example : Nat.le 0 5 :=
  Nat.pred_le_pred 0 5
    (Nat.le.step 1 5
      (Nat.le.step 1 4
        (Nat.le.step 1 3
          (Nat.le.step 1 2
            (Nat.le.step 1 1 (Nat.le.refl 1))))))

-- ============================================================
-- Nat.lt_irrefl: Nat.lt n n → False, i.e. nothing is < itself.
--
-- Induct on n.  Because h : Le (succ n) n depends on n, auto-revert
-- pulls it back into G — each branch gets a freshly-typed h binder.
-- Base: h : Le 1 0.  Use Nat.not_succ_le_zero.
-- Step: h : Le (succ (succ k)) (succ k).  pred_le_pred drops a succ
-- off both, giving Le (succ k) k, which is Nat.lt k k, dispatched by
-- the IH.
-- ============================================================

theorem Nat.lt_irrefl : (n : Nat) -> Nat.lt n n -> False :=
  by intro n; intro h;
     induction n;
     -- base branch: h : Nat.lt 0 0 = Le 1 0.
     intro h;
     exact (Nat.not_succ_le_zero 0 h);
     -- step branch: ih : Π h:Le (succ k) k. False.  h : Le (succ (succ k)) (succ k).
     intro k; intro ih; intro h;
     exact (ih (Nat.pred_le_pred (Nat.succ k) k h))

example : False -> Nat :=
  fun (_ : False) => 0

-- Sanity that lt_irrefl produces False given a (fake) proof.
-- We can't actually call lt_irrefl 5 with a real proof since no such
-- proof exists; this is just a type check.
def lt_irrefl_consumer (h : Nat.lt 5 5) : Nat :=
  False.rec.{1} (fun (_ : False) => Nat) (Nat.lt_irrefl 5 h)

-- ============================================================
-- Nat.le_antisymm: m ≤ n → n ≤ m → m = n.
--
-- Induct on h1.  Auto-revert pulls h2 (depends on n, an index of h1)
-- back into G.
-- Refl branch: h2 specialises to `Le m m`, goal `Eq m m`, just refl.
-- Step branch: have h_inner : Le m m1 and h2 : Le (succ m1) m.
-- Chain via le_trans: Le (succ m1) m1 = Lt m1 m1.  Apply lt_irrefl
-- to derive False, then False.rec to absurd-prove the goal.
-- ============================================================

theorem Nat.le_antisymm : (m : Nat) -> (n : Nat) ->
    Nat.le m n -> Nat.le n m -> Eq.{1} Nat m n :=
  by intro m; intro n; intro h1; intro h2;
     induction h1;
     -- refl: minor = Π h2 : Le m m. Eq Nat m m.
     intro h2;
     apply Eq.refl;
     -- step: m1, h_inner, ih, h2 : Le (succ m1) m. Goal Eq Nat m (succ m1).
     intro m1; intro h_inner; intro ih; intro h2;
     exact (@False.rec.{0}
              (fun (_ : False) => Eq.{1} Nat m (Nat.succ m1))
              (Nat.lt_irrefl m1
                (Nat.le_trans (Nat.succ m1) m m1 h2 h_inner)))

example : Eq.{1} Nat 3 3 :=
  Nat.le_antisymm 3 3 (Nat.le.refl 3) (Nat.le.refl 3)
