-- `induction h` now handles concrete (non-FVar) indices via index
-- unification.  Mechanism: for each concrete index in h's type, allocate
-- a fresh FVar k_new, replace the concrete value in the goal with k_new,
-- wrap the goal in a `Π h_eq : Eq T orig k_new` binder, then run the
-- standard motive-build.  The recursor's result type becomes
-- `Π h_eqs, G`, which we apply to `Eq.refl orig` arguments to recover G.
--
-- The user-facing effect: in each branch they get extra `h_eq`
-- hypotheses to discharge — either constructively (refl, when the
-- branch's pattern actually matches the original index) or by deriving
-- False (when the branch's pattern is impossible).

-- ============================================================
-- Nat.le_zero: a ≤ 0 → a = 0.  The classic case that wants index
-- unification: the index is the concrete `0`.
-- ============================================================

theorem Nat.le_zero (n : Nat) (h : Nat.le n Nat.zero) : Eq.{1} Nat n Nat.zero :=
  by induction h;
     -- refl branch: motive at (k=n, refl) gives `Eq Nat 0 n → Eq Nat n n`.
     -- The body's `n` was the orig 0 replaced by k=n in the goal; we
     -- close with Eq.refl.
     intro h_eq;
     apply Eq.refl;
     -- step branch: motive at (k=succ m, step n m h') gives
     -- `Eq Nat 0 (succ m) → Eq Nat n (succ m)`.  Derive False from
     -- h_eq's impossible 0 = succ m, then use False.rec.
     intro m; intro h_inner; intro ih; intro h_eq;
     exact (@False.rec.{0}
              (fun (_ : False) => Eq.{1} Nat n (Nat.succ m))
              (succ_ne_zero m
                (@Eq.symm.{1} Nat Nat.zero (Nat.succ m) h_eq)))

example : Eq.{1} Nat 0 0 := Nat.le_zero 0 (Nat.le.refl 0)

-- ============================================================
-- Nat.not_succ_le_zero: succ n ≤ 0 → False.  Like le_zero, but the
-- conclusion is False so both refl and step branches must show False
-- — refl is impossible because index 0 ≠ param succ n.
-- ============================================================

theorem Nat.not_succ_le_zero (n : Nat)
    (h : Nat.le (Nat.succ n) Nat.zero) : False :=
  by induction h;
     -- refl branch: motive(k=succ n, refl) = `Eq Nat 0 (succ n) → False`.
     -- 0 = succ n is impossible (the goal IS False, no need to wrap).
     intro h_eq;
     exact (succ_ne_zero n
              (@Eq.symm.{1} Nat Nat.zero (Nat.succ n) h_eq));
     -- step branch: motive(k=succ m, step (succ n) m h') = `Eq Nat 0 (succ m) → False`.
     intro m; intro h_inner; intro ih; intro h_eq;
     exact (succ_ne_zero m
              (@Eq.symm.{1} Nat Nat.zero (Nat.succ m) h_eq))

-- Nat.lt n n = Nat.le (succ n) n; an instance of not_succ_le_zero
-- needs a different formulation (lt_irrefl induces on n, not on h).
-- Skipped here.

-- ============================================================
-- Sanity: when ALL indices are FVars, the new code path falls through
-- to the unchanged FVar-only logic.  Re-run Nat.succ_le_succ as a
-- regression check.
-- ============================================================

theorem Nat.succ_le_succ_redo (n m : Nat) (h : Nat.le n m) :
    Nat.le (Nat.succ n) (Nat.succ m) :=
  by induction h;
     apply Nat.le.refl;
     intro k; intro h_inner; intro ih;
     apply Nat.le.step;
     exact ih
