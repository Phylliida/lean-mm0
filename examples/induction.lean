-- The `induction h` tactic.  Like `cases h` but with a *dependent*
-- motive: each subgoal's goal is the original goal with `h` replaced
-- by the constructor pattern, and each recursive-field hypothesis
-- (IH) has type "the goal at that sub-term" rather than the abstract
-- original.  This makes it useful for actual proofs (cases v2's
-- non-dependent motive leaves the goal unchanged in every branch,
-- so the user can't reason about the specific constructor).
--
-- Each constructor's subgoal is `Π fields, Π ihs, G[h := ctor fields]`.
-- The user `intro`s the fields and IHs manually, just like with cases v2.

-- ============================================================
-- zero_add: 0 + n = n.  Same statement math.lean proves with a hand-
-- written Nat.rec; here we drive it with the induction tactic.
-- ============================================================

theorem zero_add_by_induction (n : Nat) : Eq.{1} Nat (Nat.add 0 n) n :=
  by induction n;
     -- base case: 0 + 0 = 0  (by refl)
     apply Eq.refl;
     -- step case: subgoal of type Π k, Π ih : 0+k=k, 0 + succ k = succ k
     intro k; intro ih;
     -- 0 + succ k def-reduces to succ (0 + k); by ih it = succ k.
     apply lift_succ;
     exact ih

example : Eq.{1} Nat (Nat.add 0 5) 5 := zero_add_by_induction 5

-- ============================================================
-- A property about Bool: a non-recursive induction (= cases with
-- dependent motive).  Confirms induction works for non-recursive
-- inductives too — both branches have zero IHs and zero fields.
-- ============================================================

theorem bool_not_not (b : Bool) :
    Eq.{1} Bool (Bool.not (Bool.not b)) b :=
  by induction b;
     -- false case: not (not false) = not true = false
     apply Eq.refl;
     -- true case
     apply Eq.refl

example : Eq.{1} Bool (Bool.not (Bool.not Bool.true)) Bool.true :=
  bool_not_not Bool.true

-- ============================================================
-- A list-shape induction: `length (append xs ys) = length xs + length ys`.
-- For each ctor the subgoal is specialised to the constructor pattern.
-- `length` and `append` come from list_ops.lean (top-level polymorphic
-- definitions, not under `List`).
-- ============================================================

theorem length_append (xs ys : List.{1} Nat) :
    Eq.{1} Nat (@length.{1} Nat (@append.{1} Nat xs ys))
               (Nat.add (@length.{1} Nat xs) (@length.{1} Nat ys)) :=
  by induction xs;
     -- nil case: length (append nil ys) = 0 + length ys
     --   LHS def-reduces to length ys (append nil ys = ys).
     --   RHS = 0 + length ys — not def-eq.
     --   So we use Eq.symm of zero_add_by_induction.
     apply Eq.symm; apply zero_add_by_induction;
     -- cons case: intro hd; intro tl; intro ih
     --   LHS def-reduces to: succ (length (append tl ys)).
     --   RHS: (succ (length tl)) + length ys.  Nat.add doesn't reduce here
     --   (its second arg, length ys, isn't a constructor).
     -- We can't use `rewrite` directly because the rewrite tactic operates
     -- on the syntactic goal (post-β only) and can't see through the
     -- non-reduced `length (cons hd tl)` / `append (cons hd tl) ys`.
     -- Build the proof by Eq.trans + lift_succ + Eq.symm succ_add and let
     -- the kernel's def-eq absorb the unfolding on both sides.
     intro hd; intro tl; intro ih;
     exact (@Eq.trans.{1} Nat
              (@length.{1} Nat (@append.{1} Nat
                (List.cons.{1} Nat hd tl) ys))
              (Nat.succ (Nat.add (@length.{1} Nat tl)
                                 (@length.{1} Nat ys)))
              (Nat.add (@length.{1} Nat (List.cons.{1} Nat hd tl))
                       (@length.{1} Nat ys))
              (lift_succ (@length.{1} Nat (@append.{1} Nat tl ys))
                         (Nat.add (@length.{1} Nat tl) (@length.{1} Nat ys))
                         ih)
              (Eq.symm.{1} Nat
                (Nat.add (Nat.succ (@length.{1} Nat tl))
                         (@length.{1} Nat ys))
                (Nat.succ (Nat.add (@length.{1} Nat tl)
                                   (@length.{1} Nat ys)))
                (succ_add (@length.{1} Nat tl) (@length.{1} Nat ys))))

example :
    Eq.{1} Nat
      (@length.{1} Nat
        (@append.{1} Nat
          (List.cons.{1} Nat 1 (List.cons.{1} Nat 2 (List.nil.{1} Nat)))
          (List.cons.{1} Nat 3 (List.nil.{1} Nat))))
      3 :=
  Eq.refl.{1} Nat 3

-- ============================================================
-- succ_add via induction.  Same theorem math.lean proves with a hand-
-- written Nat.rec; here we drive it with `induction` + the
-- `apply lift_succ; exact ih` pattern (which would historically have
-- lost `ih` under the eager wrap design).  An outer FVar `m` plus the
-- subgoal-local `k`, `ih` exercises the close-at-the-right-depth path.
-- ============================================================

theorem succ_add_by_induction (m n : Nat) :
    Eq.{1} Nat (Nat.add (Nat.succ m) n) (Nat.succ (Nat.add m n)) :=
  by induction n;
     -- base: succ m + 0 = succ (m + 0) — both sides def-reduce to succ m.
     apply Eq.refl;
     -- step: ih : succ m + k = succ (m + k).
     -- Goal: succ m + succ k = succ (m + succ k)
     --   ≡ succ (succ m + k) = succ (succ (m + k))    [def]
     --   ≡ succ X = succ Y    where X = succ m + k, Y = succ (m + k)
     -- By IH X = Y, so lift_succ + exact ih.
     intro k; intro ih;
     apply lift_succ;
     exact ih

