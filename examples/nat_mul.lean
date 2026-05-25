-- Nat multiplication: succ_mul, mul_comm, left_distrib, mul_assoc,
-- right_distrib.  Builds on math.lean (zero_add, succ_add, add_comm)
-- and nat_lemmas.lean (add_zero, mul_zero, zero_mul, mul_one, add_assoc,
-- lift_succ).
--
-- All proofs are declared with `theorem`, which emits as MM0 `opaque-def`
-- — the verifier doesn't δ-unfold lemma bodies at every call site.
-- Without this distinction, each subsequent lemma re-normalises the entire
-- chain of prior proofs, and verification of mul_comm alone takes minutes.

-- ============================================================
-- add_left_comm: a + (b + c) = b + (a + c).
-- ============================================================

theorem add_left_comm (a b c : Nat) :
    Eq.{1} Nat (Nat.add a (Nat.add b c)) (Nat.add b (Nat.add a c)) :=
  by rewrite (Eq.symm.{1} Nat (Nat.add (Nat.add a b) c)
                              (Nat.add a (Nat.add b c))
                              (add_assoc a b c));
     rewrite (add_comm a b);
     apply add_assoc

-- ============================================================
-- succ_mul: (succ m) * n = n + m*n.  Induction on n.
--
-- Chain (each step is either def-eq, succ_add, lift_succ ∘ add_left_comm,
-- or Eq.symm succ_add):
--   mul (succ m) (succ k)
--   ≡ add (succ m) (mul (succ m) k)         [def: mul on succ]
--   = add (succ m) (add k (mul m k))        [lift ih]
--   = succ (add m (add k (mul m k)))        [succ_add]
--   = succ (add k (add m (mul m k)))        [lift_succ ∘ add_left_comm]
--   = add (succ k) (add m (mul m k))        [Eq.symm succ_add]
--   ≡ add (succ k) (mul m (succ k))         [def]
-- ============================================================

theorem succ_mul (m n : Nat) :
    Eq.{1} Nat (Nat.mul (Nat.succ m) n) (Nat.add n (Nat.mul m n)) :=
  @Nat.rec.{0}
    (fun (k : Nat) =>
       Eq.{1} Nat (Nat.mul (Nat.succ m) k) (Nat.add k (Nat.mul m k)))
    (Eq.refl.{1} Nat 0)
    (fun (k : Nat)
         (ih : Eq.{1} Nat (Nat.mul (Nat.succ m) k) (Nat.add k (Nat.mul m k))) =>
      @Eq.trans.{1} Nat
        (Nat.mul (Nat.succ m) (Nat.succ k))
        (Nat.add (Nat.succ m) (Nat.add k (Nat.mul m k)))
        (Nat.add (Nat.succ k) (Nat.mul m (Nat.succ k)))
        -- Step A: lift ih through (add (succ m) _).
        (@Eq.rec.{1, 0} Nat (Nat.mul (Nat.succ m) k)
          (fun (x : Nat) (_ : Eq.{1} Nat (Nat.mul (Nat.succ m) k) x) =>
             Eq.{1} Nat (Nat.mul (Nat.succ m) (Nat.succ k))
                        (Nat.add (Nat.succ m) x))
          (Eq.refl.{1} Nat (Nat.mul (Nat.succ m) (Nat.succ k)))
          (Nat.add k (Nat.mul m k)) ih)
        -- Step B: succ_add ∘ (lift_succ ∘ add_left_comm) ∘ Eq.symm succ_add.
        (@Eq.trans.{1} Nat
          (Nat.add (Nat.succ m) (Nat.add k (Nat.mul m k)))
          (Nat.succ (Nat.add k (Nat.add m (Nat.mul m k))))
          (Nat.add (Nat.succ k) (Nat.mul m (Nat.succ k)))
          (@Eq.trans.{1} Nat
            (Nat.add (Nat.succ m) (Nat.add k (Nat.mul m k)))
            (Nat.succ (Nat.add m (Nat.add k (Nat.mul m k))))
            (Nat.succ (Nat.add k (Nat.add m (Nat.mul m k))))
            (succ_add m (Nat.add k (Nat.mul m k)))
            (lift_succ
              (Nat.add m (Nat.add k (Nat.mul m k)))
              (Nat.add k (Nat.add m (Nat.mul m k)))
              (add_left_comm m k (Nat.mul m k))))
          (Eq.symm.{1} Nat
            (Nat.add (Nat.succ k) (Nat.mul m (Nat.succ k)))
            (Nat.succ (Nat.add k (Nat.add m (Nat.mul m k))))
            (succ_add k (Nat.add m (Nat.mul m k))))))
    n

example : Eq.{1} Nat (Nat.mul 3 4) (Nat.add 4 (Nat.mul 2 4)) := succ_mul 2 4

-- ============================================================
-- mul_comm: m * n = n * m.  Induction on n.
-- Step: ih : m*k = k*m.  Goal: m*(succ k) = (succ k)*m.
--   LHS def-reduces to add m (mul m k); lift ih -> add m (mul k m).
--   Eq.symm of succ_mul k m: (succ k)*m = add m (k*m), so
--     add m (mul k m) = (succ k) * m.
-- ============================================================

theorem mul_comm (m n : Nat) : Eq.{1} Nat (Nat.mul m n) (Nat.mul n m) :=
  @Nat.rec.{0}
    (fun (k : Nat) => Eq.{1} Nat (Nat.mul m k) (Nat.mul k m))
    (Eq.symm.{1} Nat (Nat.mul 0 m) 0 (zero_mul m))
    (fun (k : Nat) (ih : Eq.{1} Nat (Nat.mul m k) (Nat.mul k m)) =>
      @Eq.trans.{1} Nat
        (Nat.mul m (Nat.succ k))
        (Nat.add m (Nat.mul k m))
        (Nat.mul (Nat.succ k) m)
        (@Eq.rec.{1, 0} Nat (Nat.mul m k)
          (fun (x : Nat) (_ : Eq.{1} Nat (Nat.mul m k) x) =>
             Eq.{1} Nat (Nat.mul m (Nat.succ k)) (Nat.add m x))
          (Eq.refl.{1} Nat (Nat.mul m (Nat.succ k)))
          (Nat.mul k m) ih)
        (Eq.symm.{1} Nat (Nat.mul (Nat.succ k) m) (Nat.add m (Nat.mul k m))
          (succ_mul k m)))
    n

example : Eq.{1} Nat (Nat.mul 3 5) (Nat.mul 5 3) := mul_comm 3 5

-- ============================================================
-- left_distrib: a * (b + c) = a*b + a*c.  Induction on c.
-- Step: a*(b + succ k) = a*b + a*(succ k).
--   LHS def-reduces (add b (succ k) = succ (add b k); mul a (succ _)
--   = add a (mul a _)) to add a (mul a (add b k)).
--   Lift ih -> add a (add (mul a b) (mul a k)).
--   add_left_comm a (a*b) (a*k): = add (a*b) (add a (a*k)),
--   which def-eq RHS.
-- ============================================================

theorem left_distrib (a b c : Nat) :
    Eq.{1} Nat (Nat.mul a (Nat.add b c))
               (Nat.add (Nat.mul a b) (Nat.mul a c)) :=
  @Nat.rec.{0}
    (fun (k : Nat) =>
       Eq.{1} Nat (Nat.mul a (Nat.add b k))
                  (Nat.add (Nat.mul a b) (Nat.mul a k)))
    (Eq.refl.{1} Nat (Nat.mul a b))
    (fun (k : Nat)
         (ih : Eq.{1} Nat (Nat.mul a (Nat.add b k))
                          (Nat.add (Nat.mul a b) (Nat.mul a k))) =>
      @Eq.trans.{1} Nat
        (Nat.mul a (Nat.add b (Nat.succ k)))
        (Nat.add a (Nat.add (Nat.mul a b) (Nat.mul a k)))
        (Nat.add (Nat.mul a b) (Nat.mul a (Nat.succ k)))
        (@Eq.rec.{1, 0} Nat (Nat.mul a (Nat.add b k))
          (fun (x : Nat) (_ : Eq.{1} Nat (Nat.mul a (Nat.add b k)) x) =>
             Eq.{1} Nat (Nat.mul a (Nat.add b (Nat.succ k))) (Nat.add a x))
          (Eq.refl.{1} Nat (Nat.mul a (Nat.add b (Nat.succ k))))
          (Nat.add (Nat.mul a b) (Nat.mul a k)) ih)
        (add_left_comm a (Nat.mul a b) (Nat.mul a k)))
    c

example : Eq.{1} Nat (Nat.mul 3 (Nat.add 4 5))
                     (Nat.add (Nat.mul 3 4) (Nat.mul 3 5)) :=
  left_distrib 3 4 5

-- ============================================================
-- mul_assoc: (a * b) * c = a * (b * c).  Induction on c.
-- Step: (a*b)*(succ k) = a*(b*(succ k))
--   LHS def-reduces to add (a*b) ((a*b)*k); lift ih -> add (a*b) (a*(b*k)).
--   Eq.symm of left_distrib a b (b*k):  a*(add b (b*k)) = add (a*b) (a*(b*k)).
--   RHS def-eq a*(add b (b*k)).
-- ============================================================

theorem mul_assoc (a b c : Nat) :
    Eq.{1} Nat (Nat.mul (Nat.mul a b) c) (Nat.mul a (Nat.mul b c)) :=
  @Nat.rec.{0}
    (fun (k : Nat) =>
       Eq.{1} Nat (Nat.mul (Nat.mul a b) k) (Nat.mul a (Nat.mul b k)))
    (Eq.refl.{1} Nat 0)
    (fun (k : Nat)
         (ih : Eq.{1} Nat (Nat.mul (Nat.mul a b) k) (Nat.mul a (Nat.mul b k))) =>
      @Eq.trans.{1} Nat
        (Nat.mul (Nat.mul a b) (Nat.succ k))
        (Nat.add (Nat.mul a b) (Nat.mul a (Nat.mul b k)))
        (Nat.mul a (Nat.mul b (Nat.succ k)))
        (@Eq.rec.{1, 0} Nat (Nat.mul (Nat.mul a b) k)
          (fun (x : Nat) (_ : Eq.{1} Nat (Nat.mul (Nat.mul a b) k) x) =>
             Eq.{1} Nat (Nat.mul (Nat.mul a b) (Nat.succ k))
                        (Nat.add (Nat.mul a b) x))
          (Eq.refl.{1} Nat (Nat.mul (Nat.mul a b) (Nat.succ k)))
          (Nat.mul a (Nat.mul b k)) ih)
        (Eq.symm.{1} Nat
          (Nat.mul a (Nat.add b (Nat.mul b k)))
          (Nat.add (Nat.mul a b) (Nat.mul a (Nat.mul b k)))
          (left_distrib a b (Nat.mul b k))))
    c

example : Eq.{1} Nat (Nat.mul (Nat.mul 2 3) 4) (Nat.mul 2 (Nat.mul 3 4)) :=
  mul_assoc 2 3 4

-- ============================================================
-- right_distrib: (a + b) * c = a*c + b*c.  Reduces to left_distrib via
-- mul_comm.
-- ============================================================

theorem right_distrib (a b c : Nat) :
    Eq.{1} Nat (Nat.mul (Nat.add a b) c)
               (Nat.add (Nat.mul a c) (Nat.mul b c)) :=
  by rewrite (mul_comm (Nat.add a b) c);
     rewrite (left_distrib c a b);
     rewrite (mul_comm c a);
     rewrite (mul_comm c b);
     apply Eq.refl

example : Eq.{1} Nat (Nat.mul (Nat.add 2 3) 4)
                     (Nat.add (Nat.mul 2 4) (Nat.mul 3 4)) :=
  right_distrib 2 3 4
