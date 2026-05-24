-- Genuine math content: actual induction proofs over Nat using Nat.rec.
-- These are the kinds of theorems mathlib's Nat namespace is built from.

-- The easy facts hold by definitional equality.  Nat.add was defined as
--   add m n = Nat.rec (λ _. Nat) m (succ-step) n
-- so `add m 0` immediately reduces to `m`.
example : Eq.{1} Nat (Nat.add 5 0) 5 := Eq.refl.{1} Nat 5

-- Similarly, `add m (succ n)` reduces to `succ (add m n)` by ι.
example (m n : Nat) : Eq.{1} Nat (Nat.add m (Nat.succ n))
                                  (Nat.succ (Nat.add m n)) :=
  Eq.refl.{1} Nat (Nat.succ (Nat.add m n))

-- A computation chain check
example : Eq.{1} Nat (Nat.add 7 (Nat.add 8 9)) 24 := Eq.refl.{1} Nat 24

-- The HARD one: `0 + n = n` for ALL n.  This is NOT definitional —
-- it requires induction on n.  Use Nat.rec directly with motive
-- `λ n. Eq Nat (0 + n) n`.
def zero_add (n : Nat) : Eq.{1} Nat (Nat.add 0 n) n :=
  @Nat.rec.{0}
    (fun (k : Nat) => Eq.{1} Nat (Nat.add 0 k) k)
    (Eq.refl.{1} Nat 0)
    (fun (k : Nat) (ih : Eq.{1} Nat (Nat.add 0 k) k) =>
       -- Goal: Eq Nat (0 + succ k) (succ k)
       -- By definition, 0 + succ k = succ (0 + k).  So we need
       -- Eq Nat (succ (0 + k)) (succ k), which follows from `ih`
       -- via Eq.rec, abstracting `(0 + k)` out of the goal.
       @Eq.rec.{1, 0} Nat (Nat.add 0 k)
         (fun (x : Nat) (_ : Eq.{1} Nat (Nat.add 0 k) x) =>
            Eq.{1} Nat (Nat.succ (Nat.add 0 k)) (Nat.succ x))
         (Eq.refl.{1} Nat (Nat.succ (Nat.add 0 k)))
         k ih)
    n

-- And we can check a specific instance reduces too
example : Eq.{1} Nat (Nat.add 0 7) 7 := zero_add 7
