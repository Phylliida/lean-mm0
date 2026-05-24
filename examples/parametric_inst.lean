-- Parametric instances + recursive instance synthesis with backtracking.
--
-- The classic example: given `Add α` and `Add β`, derive `Add (Pair α β)`
-- by component-wise addition.  The user writes `1 + 2 : Pair Nat Nat`
-- (in some form) and the elaborator searches `addProd` → recursively
-- finds two `Add Nat` instances.

class Add.{u} (a : Sort u) : Sort u where
  add : a -> a -> a

structure Pair.{u, v} (a : Sort u) (b : Sort v) : Sort (max u v) where
  (fst : a)
  (snd : b)

instance addNat : Add.{1} Nat := Add.mk.{1} Nat Nat.add

-- The parametric instance: needs [Add α] and [Add β] to deliver Add (Pair α β).
instance addPair.{u, v} {a : Sort u} {b : Sort v}
    [_ia : Add.{u} a] [_ib : Add.{v} b] : Add.{max u v} (Pair.{u, v} a b) :=
  Add.mk.{max u v} (Pair.{u, v} a b)
    (fun (p q : Pair.{u, v} a b) =>
       Pair.mk.{u, v} a b
         (@Add.add.{u} a _ia (Pair.fst.{u, v} a b p) (Pair.fst.{u, v} a b q))
         (@Add.add.{v} b _ib (Pair.snd.{u, v} a b p) (Pair.snd.{u, v} a b q)))

infixl:65 + Add.add

-- Build two pairs of Nats
def p1 : Pair.{1, 1} Nat Nat := Pair.mk.{1, 1} Nat Nat 1 2
def p2 : Pair.{1, 1} Nat Nat := Pair.mk.{1, 1} Nat Nat 10 20

-- Use the synthesised Add (Pair Nat Nat) instance.  The elaborator
-- finds addPair (after backtracking past addNat), then recursively
-- finds Add Nat = addNat for both implicit args.
def sum_pair : Pair.{1, 1} Nat Nat := p1 + p2

-- Verify by projection
theorem sum_fst : Eq.{1} Nat (Pair.fst.{1, 1} Nat Nat sum_pair) 11 :=
  Eq.refl.{1} Nat 11

theorem sum_snd : Eq.{1} Nat (Pair.snd.{1, 1} Nat Nat sum_pair) 22 :=
  Eq.refl.{1} Nat 22
