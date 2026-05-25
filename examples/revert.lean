-- The `revert h` tactic.  Inverse of `intro`: pulls a hypothesis
-- intro'd earlier in the same tactic block back into the goal as a
-- leading Π binder.  Useful before `induction` when an extra
-- hypothesis depends on what we're inducting over.
--
-- Limitations:
--   - Only works on hypotheses *introduced by `intro`* in this `by`
--     block.  Theorem binders cannot be reverted (would conflict with
--     the def's outer Lam wrap).
--   - When the named hypothesis isn't the most recent intro, every
--     later intro is reverted too (in reverse order).

-- ============================================================
-- Trivial revert: intro a Nat, revert it, then re-intro and use it.
-- The goal before revert is Nat (the def's return type); after
-- revert it's Nat → Nat (we've moved x into the Π).
-- ============================================================

def revert_then_intro : Nat -> Nat :=
  by intro x;
     revert x;
     intro y;
     exact y

example : Eq.{1} Nat (revert_then_intro 7) 7 := by rfl

-- ============================================================
-- Revert + induction: a classic use of revert.  Prove
-- `add_comm m n` by inducting on n.  Without revert the IH at the
-- step case would have a fixed m (whatever m is from the outer
-- context); reverting m before the induction gives an IH quantified
-- over all m', i.e. the natural induction-on-n statement.
--
-- The hand-written math.lean add_comm already does this trick
-- implicitly with a manual Nat.rec.  Here we drive it with the
-- tactics.
-- ============================================================

-- We state the theorem with `n` as the OUTER binder because
-- `revert m; induction n` makes `n` the outer abstraction in the
-- recursor application — the resulting term's leading Π is over n.
-- The standard `add_comm (m n : Nat) : ...` shape could be matched
-- by wrapping the result with extra revert/intro juggling, but here
-- we just align the def's signature with the proof's natural shape.
theorem add_comm_via_revert :
    (n : Nat) -> (m : Nat) -> Eq.{1} Nat (Nat.add m n) (Nat.add n m) :=
  by intro n; intro m;
     revert m;
     induction n;
     -- base: Π m, m + 0 = 0 + m.  LHS def-reduces to m; RHS needs zero_add.
     intro m;
     apply Eq.symm; apply zero_add;
     -- step: Π k, Π ih : (Π m, m+k = k+m), Π m, m + succ k = succ k + m.
     intro k; intro ih; intro m;
     -- LHS m+succ k = succ (m+k) by def.
     -- RHS succ k + m = succ (k+m) by succ_add.
     -- ih m: m + k = k + m.  Lift through succ: succ (m+k) = succ (k+m).
     -- Then Eq.symm of succ_add gives succ (k+m) = succ k + m.
     exact (@Eq.trans.{1} Nat
              (Nat.add m (Nat.succ k))
              (Nat.succ (Nat.add k m))
              (Nat.add (Nat.succ k) m)
              (lift_succ (Nat.add m k) (Nat.add k m) (ih m))
              (Eq.symm.{1} Nat
                (Nat.add (Nat.succ k) m)
                (Nat.succ (Nat.add k m))
                (succ_add k m)))

example : Eq.{1} Nat (Nat.add 3 5) (Nat.add 5 3) := add_comm_via_revert 5 3
