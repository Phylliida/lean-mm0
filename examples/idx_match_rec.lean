-- Indexed-inductive match v2: extends the v1 indexed match to handle
-- constructors with recursive fields.  The IH is auto-bound as an extra
-- synthetic lambda after the field binders; its type is
-- `motive idx_for_rec_call rec_field`, with the idx values coming from
-- the recursor rule's `rec_index_templates`.
--
-- Before this change `match` on Nat.le.step (or Vec.cons, etc.) was
-- rejected with "not yet supported (use the recursor directly)".
-- Now the user can write Nat.le matches directly.

-- ============================================================
-- Test 1: non-IH-using match.  The step ctor's IH binder is auto-
-- wrapped but the RHS doesn't reference it.  Exercises the basic
-- shape of the new minor.
-- ============================================================

def Nat.le_to_zero (n m : Nat) (h : Nat.le n m) : Nat :=
  match (motive := fun (k : Nat) (_ : Nat.le n k) => Nat) h with
  | Nat.le.refl       => 0
  | Nat.le.step m1 h1 => 0

example : Eq.{1} Nat (Nat.le_to_zero 0 0 (Nat.le.refl 0)) 0 :=
  Eq.refl.{1} Nat 0
example : Eq.{1} Nat (Nat.le_to_zero 0 1 (Nat.le.step 0 0 (Nat.le.refl 0))) 0 :=
  Eq.refl.{1} Nat 0

-- ============================================================
-- Test 2: an IH-using recursive function.  `Nat.le_diff n m h` counts
-- the number of `step` constructors between n and m (i.e., m - n in
-- the success case).  The recursive call `Nat.le_diff n m1 h1` is
-- detected by the structural-recursion sentinel substitution and
-- becomes the IH BVar.  This exercises the full
-- rec_index_templates → ih_ty plumbing.
-- ============================================================

def Nat.le_diff (n m : Nat) (h : Nat.le n m) : Nat :=
  match (motive := fun (k : Nat) (_ : Nat.le n k) => Nat) h with
  | Nat.le.refl       => 0
  | Nat.le.step m1 h1 => Nat.succ (Nat.le_diff n m1 h1)

-- Sanity: diff from 0 to 3 should be 3 (one `step` per increment).
example : Eq.{1} Nat
    (Nat.le_diff 0 3
       (Nat.le.step 0 2
         (Nat.le.step 0 1
           (Nat.le.step 0 0 (Nat.le.refl 0)))))
    3 := Eq.refl.{1} Nat 3

-- And diff from 2 to 2 (the refl case) should be 0.
example : Eq.{1} Nat (Nat.le_diff 2 2 (Nat.le.refl 2)) 0 :=
  Eq.refl.{1} Nat 0

-- ============================================================
-- Test 3: Vec.  Exercises a *different* indexed inductive whose
-- recursive ctor has multiple non-rec fields (n, h) and a rec field
-- (t).  rec_index_templates[0] = (BVar(2),) = n (in ctor's field-
-- binder convention) — the IH ty becomes `motive n t`, indexed by n
-- not by the cons's own index `succ n`.
-- ============================================================

def Vec_length_match.{u} (a : Sort u) (n : Nat) (v : Vec.{u} a n) : Nat :=
  match (motive := fun (k : Nat) (_ : Vec.{u} a k) => Nat) v with
  | Vec.nil          => 0
  | Vec.cons n1 h t1 => Nat.succ (Vec_length_match a n1 t1)

def my_pair_v : Vec.{1} Nat 2 :=
  Vec.cons.{1} Nat 1 7 (Vec.cons.{1} Nat 0 8 (Vec.nil.{1} Nat))

example : Eq.{1} Nat (Vec_length_match.{1} Nat 2 my_pair_v) 2 :=
  Eq.refl.{1} Nat 2

example : Eq.{1} Nat (Vec_length_match.{1} Nat 0 (Vec.nil.{1} Nat)) 0 :=
  Eq.refl.{1} Nat 0
