-- Genuine math content: real induction proofs over Nat.  These are
-- the kinds of theorems mathlib's `Nat.*` namespace is built from.

-- ============================================================
-- Computational facts that hold by definitional equality.
-- ============================================================

example : Eq.{1} Nat (Nat.add 5 0) 5 := Eq.refl.{1} Nat 5

example (m n : Nat) : Eq.{1} Nat (Nat.add m (Nat.succ n))
                                  (Nat.succ (Nat.add m n)) :=
  Eq.refl.{1} Nat (Nat.succ (Nat.add m n))

example : Eq.{1} Nat (Nat.add 7 (Nat.add 8 9)) 24 := Eq.refl.{1} Nat 24

-- ============================================================
-- Lemma 1: 0 + n = n  (the canonical first non-trivial fact).
-- The reverse direction (n + 0 = n) is free by definition.
-- ============================================================

def zero_add (n : Nat) : Eq.{1} Nat (Nat.add 0 n) n :=
  @Nat.rec.{0}
    (fun (k : Nat) => Eq.{1} Nat (Nat.add 0 k) k)
    (Eq.refl.{1} Nat 0)
    (fun (k : Nat) (ih : Eq.{1} Nat (Nat.add 0 k) k) =>
       @Eq.rec.{1, 0} Nat (Nat.add 0 k)
         (fun (x : Nat) (_ : Eq.{1} Nat (Nat.add 0 k) x) =>
            Eq.{1} Nat (Nat.succ (Nat.add 0 k)) (Nat.succ x))
         (Eq.refl.{1} Nat (Nat.succ (Nat.add 0 k)))
         k ih)
    n

example : Eq.{1} Nat (Nat.add 0 7) 7 := zero_add 7

-- ============================================================
-- Lemma 2: (succ m) + n = succ (m + n)  by induction on n.
-- ============================================================

def succ_add (m n : Nat) :
    Eq.{1} Nat (Nat.add (Nat.succ m) n) (Nat.succ (Nat.add m n)) :=
  @Nat.rec.{0}
    (fun (k : Nat) =>
       Eq.{1} Nat (Nat.add (Nat.succ m) k) (Nat.succ (Nat.add m k)))
    -- base: succ m + 0 = succ m = succ (m + 0)  (both reduce)
    (Eq.refl.{1} Nat (Nat.succ m))
    -- step: ih lifted through Nat.succ via Eq.rec
    (fun (k : Nat)
         (ih : Eq.{1} Nat (Nat.add (Nat.succ m) k) (Nat.succ (Nat.add m k))) =>
       @Eq.rec.{1, 0} Nat (Nat.add (Nat.succ m) k)
         (fun (x : Nat) (_ : Eq.{1} Nat (Nat.add (Nat.succ m) k) x) =>
            Eq.{1} Nat (Nat.succ (Nat.add (Nat.succ m) k)) (Nat.succ x))
         (Eq.refl.{1} Nat (Nat.succ (Nat.add (Nat.succ m) k)))
         (Nat.succ (Nat.add m k)) ih)
    n

example : Eq.{1} Nat (Nat.add (Nat.succ 4) 3) (Nat.succ (Nat.add 4 3)) :=
  succ_add 4 3

-- ============================================================
-- Lemma 3: add_comm — uses zero_add, succ_add, Eq.symm, Eq.trans.
-- ============================================================

def add_comm (m n : Nat) :
    Eq.{1} Nat (Nat.add m n) (Nat.add n m) :=
  @Nat.rec.{0}
    (fun (k : Nat) => Eq.{1} Nat (Nat.add m k) (Nat.add k m))
    -- base case: m + 0 = m = 0 + m  (use Eq.symm of zero_add)
    (@Eq.symm.{1} Nat (Nat.add 0 m) m (zero_add m))
    -- step: assume IH : m + k = k + m.  Want m + succ k = succ k + m.
    --   m + succ k  =  succ (m + k)         (refl)
    --              =  succ (k + m)         (lift IH through succ)
    --              =  succ k + m           (Eq.symm of succ_add)
    (fun (k : Nat) (ih : Eq.{1} Nat (Nat.add m k) (Nat.add k m)) =>
      @Eq.trans.{1} Nat
        (Nat.add m (Nat.succ k))                -- start
        (Nat.succ (Nat.add k m))                -- middle (after IH lift)
        (Nat.add (Nat.succ k) m)                -- end
        -- m + succ k  =  succ (k + m)   via lifting ih through succ
        (@Eq.rec.{1, 0} Nat (Nat.add m k)
          (fun (x : Nat) (_ : Eq.{1} Nat (Nat.add m k) x) =>
            Eq.{1} Nat (Nat.add m (Nat.succ k)) (Nat.succ x))
          (Eq.refl.{1} Nat (Nat.add m (Nat.succ k)))
          (Nat.add k m) ih)
        -- succ (k + m) = succ k + m   via Eq.symm of succ_add
        (@Eq.symm.{1} Nat (Nat.add (Nat.succ k) m) (Nat.succ (Nat.add k m))
          (succ_add k m)))
    n

example : Eq.{1} Nat (Nat.add 3 5) (Nat.add 5 3) := add_comm 3 5
example : Eq.{1} Nat (Nat.add 5 3) 8 := Eq.refl.{1} Nat 8
