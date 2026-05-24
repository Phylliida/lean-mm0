-- Building blocks for Nat decidable equality: succ injectivity and
-- the no-confusion principle (succ n ≠ 0).

-- Predicate that's True at 0 and False at any succ — used to transport
-- a "succ n = 0" hypothesis into a False proof.
def nat_no_confuse (m : Nat) : Prop :=
  @Nat.rec.{1} (fun (_ : Nat) => Prop) True (fun (_ : Nat) (_ : Prop) => False) m

-- Sanity: nat_no_confuse reduces.
example : Eq.{1} Prop (nat_no_confuse Nat.zero) True := Eq.refl.{1} Prop True
example : Eq.{1} Prop (nat_no_confuse (Nat.succ 5)) False := Eq.refl.{1} Prop False

-- succ n ≠ 0.
def succ_ne_zero (n : Nat) (h : Eq.{1} Nat (Nat.succ n) Nat.zero) : False :=
  @Eq.rec.{1, 0} Nat Nat.zero
    (fun (k : Nat) (_ : Eq.{1} Nat Nat.zero k) => nat_no_confuse k)
    True.intro
    (Nat.succ n)
    (@Eq.symm.{1} Nat (Nat.succ n) Nat.zero h)

-- succ is injective: succ m = succ n implies m = n.
def succ_inj (m n : Nat) (h : Eq.{1} Nat (Nat.succ m) (Nat.succ n)) :
    Eq.{1} Nat m n :=
  @Eq.rec.{1, 0} Nat (Nat.succ m)
    (fun (k : Nat) (_ : Eq.{1} Nat (Nat.succ m) k) =>
       Eq.{1} Nat m (Nat.pred k))
    (Eq.refl.{1} Nat m)
    (Nat.succ n) h
