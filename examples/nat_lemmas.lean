-- More Nat lemmas, building on math.lean's zero_add / succ_add / add_comm.
-- Pure source-side proofs.

-- ============================================================
-- Free by definition (Nat.add and Nat.mul recurse on their second arg)
-- ============================================================

def add_zero (n : Nat) : Eq.{1} Nat (Nat.add n 0) n :=
  Eq.refl.{1} Nat n

def mul_zero (n : Nat) : Eq.{1} Nat (Nat.mul n 0) 0 :=
  Eq.refl.{1} Nat 0

def mul_one (n : Nat) : Eq.{1} Nat (Nat.mul n 1) n :=
  Eq.refl.{1} Nat n

-- ============================================================
-- add_assoc: (a + b) + c = a + (b + c).  Induction on c.
-- Base: both sides reduce to a + b.
-- Step: lift IH through Nat.succ via Eq.rec.
-- ============================================================

def add_assoc (a b c : Nat) :
    Eq.{1} Nat (Nat.add (Nat.add a b) c) (Nat.add a (Nat.add b c)) :=
  @Nat.rec.{0}
    (fun (k : Nat) =>
       Eq.{1} Nat (Nat.add (Nat.add a b) k) (Nat.add a (Nat.add b k)))
    (Eq.refl.{1} Nat (Nat.add a b))
    (fun (k : Nat)
         (ih : Eq.{1} Nat (Nat.add (Nat.add a b) k) (Nat.add a (Nat.add b k))) =>
       @Eq.rec.{1, 0} Nat (Nat.add (Nat.add a b) k)
         (fun (x : Nat) (_ : Eq.{1} Nat (Nat.add (Nat.add a b) k) x) =>
            Eq.{1} Nat (Nat.succ (Nat.add (Nat.add a b) k)) (Nat.succ x))
         (Eq.refl.{1} Nat (Nat.succ (Nat.add (Nat.add a b) k)))
         (Nat.add a (Nat.add b k)) ih)
    c

example : Eq.{1} Nat (Nat.add (Nat.add 1 2) 3) (Nat.add 1 (Nat.add 2 3)) :=
  add_assoc 1 2 3

-- ============================================================
-- zero_mul: 0 * n = 0.  Induction on n.
-- Base: 0 * 0 = 0 by refl.
-- Step: 0 * (succ k) = 0 + (0 * k) = 0 + 0 [by IH] = 0.
-- The Nat.add 0 0 step is itself a definitional reduction
-- (add recurses on the second arg, but its IH lifts through succ).
-- So at the step, we need to rewrite (0 * k) to 0 via IH, then add 0 0 reduces.
-- ============================================================

def zero_mul (n : Nat) : Eq.{1} Nat (Nat.mul 0 n) 0 :=
  @Nat.rec.{0}
    (fun (k : Nat) => Eq.{1} Nat (Nat.mul 0 k) 0)
    (Eq.refl.{1} Nat 0)
    (fun (k : Nat) (ih : Eq.{1} Nat (Nat.mul 0 k) 0) =>
       -- 0 * (succ k) reduces to Nat.add 0 (0 * k).
       -- Rewrite (0 * k) to 0 via ih, then Nat.add 0 0 reduces to 0
       -- (since Nat.add 0 0 unfolds with second-arg recursion to 0).
       @Eq.rec.{1, 0} Nat (Nat.mul 0 k)
         (fun (x : Nat) (_ : Eq.{1} Nat (Nat.mul 0 k) x) =>
            Eq.{1} Nat (Nat.add 0 (Nat.mul 0 k)) (Nat.add 0 x))
         (Eq.refl.{1} Nat (Nat.add 0 (Nat.mul 0 k)))
         0 ih)
    n

example : Eq.{1} Nat (Nat.mul 0 5) 0 := zero_mul 5

-- ============================================================
-- one_mul: 1 * n = n.  Induction on n, using zero_add and a rewrite.
-- 1 * 0 = 0 by refl.
-- 1 * (succ k) = 1 + (1 * k) = 1 + k [by IH] = succ k [by succ_add + add_zero].
-- Actually 1 + k via Nat.add: recurses on k.  k=0 gives 1; k=succ j gives succ(1+j).
-- 1 + k where 1 = succ 0: by succ_add (in math.lean), succ 0 + k = succ (0 + k).
-- And 0 + k = k by zero_add.  So 1 + k = succ k.  Combine.
-- ============================================================

def one_mul (n : Nat) : Eq.{1} Nat (Nat.mul 1 n) n :=
  @Nat.rec.{0}
    (fun (k : Nat) => Eq.{1} Nat (Nat.mul 1 k) k)
    (Eq.refl.{1} Nat 0)
    (fun (k : Nat) (ih : Eq.{1} Nat (Nat.mul 1 k) k) =>
       -- 1 * (succ k) = Nat.add 1 (1 * k).  By IH, (1 * k) = k.
       -- Then Nat.add 1 k: 1 = succ 0, so this is Nat.add (succ 0) k.
       -- By succ_add: Nat.add (succ 0) k = succ (Nat.add 0 k).
       -- By zero_add (in math.lean): Nat.add 0 k = k.
       -- So Nat.add 1 k = succ k.  We need to chain these rewrites.
       --
       -- Strategy: trans of three steps
       --   1 + (1*k)  =  1 + k          via ih lifted
       --   1 + k      =  succ (0 + k)   via succ_add 0 k
       --   succ (0+k) =  succ k         via zero_add k lifted through succ
       @Eq.trans.{1} Nat
         (Nat.add 1 (Nat.mul 1 k))
         (Nat.succ (Nat.add 0 k))
         (Nat.succ k)
         (@Eq.trans.{1} Nat
            (Nat.add 1 (Nat.mul 1 k))
            (Nat.add 1 k)
            (Nat.succ (Nat.add 0 k))
            -- 1 + (1*k) = 1 + k via lifting ih
            (@Eq.rec.{1, 0} Nat (Nat.mul 1 k)
              (fun (x : Nat) (_ : Eq.{1} Nat (Nat.mul 1 k) x) =>
                 Eq.{1} Nat (Nat.add 1 (Nat.mul 1 k)) (Nat.add 1 x))
              (Eq.refl.{1} Nat (Nat.add 1 (Nat.mul 1 k)))
              k ih)
            -- 1 + k = succ (0 + k) via succ_add 0 k
            (succ_add 0 k))
         -- succ (0 + k) = succ k via lifting zero_add k
         (@Eq.rec.{1, 0} Nat (Nat.add 0 k)
           (fun (x : Nat) (_ : Eq.{1} Nat (Nat.add 0 k) x) =>
              Eq.{1} Nat (Nat.succ (Nat.add 0 k)) (Nat.succ x))
           (Eq.refl.{1} Nat (Nat.succ (Nat.add 0 k)))
           k (zero_add k)))
    n

example : Eq.{1} Nat (Nat.mul 1 4) 4 := one_mul 4

-- ============================================================
-- Same statements via the rewrite tactic — much shorter.
-- ============================================================

-- add_one (n) : 1 + n = succ n.  Two rewrites + refl.
def add_one (n : Nat) : Eq.{1} Nat (Nat.add 1 n) (Nat.succ n) :=
  by rewrite (succ_add 0 n); rewrite (zero_add n); apply Eq.refl

-- Symmetry the easy way.
def sym_via_rw.{u} {α : Sort u} (a b : α) (h : Eq.{u} α a b) :
    Eq.{u} α b a :=
  by rewrite h; apply Eq.refl

-- Apply succ to both sides of an equality.
def lift_succ (m n : Nat) (h : Eq.{1} Nat m n) :
    Eq.{1} Nat (Nat.succ m) (Nat.succ n) :=
  by rewrite h; apply Eq.refl

example : Eq.{1} Nat (Nat.add 1 5) 6 := add_one 5
