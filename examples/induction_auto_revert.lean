-- Auto-revert for `induction`.  When the user inducts on a hypothesis
-- `h : Ind params indices`, the tactic now automatically reverts every
-- local hypothesis (later in ctx than h) whose type references h
-- itself or any FVar-index of h's type.  Without this, those dependent
-- hypotheses kept their original (abstract) types in every branch,
-- making it impossible to use index specialisation through them; the
-- user had to write `revert h2; induction h1` by hand.
--
-- Transitive: if h3 depends on h2 and h2 depends on h1, both get
-- reverted.  Innermost dependents are popped first, so the final Π
-- order in each branch matches the original ctx order.
--
-- Restriction: auto-revert only acts on hypotheses introduced *inside*
-- the current `by` block (focused_intros), because pre-existing def/
-- theorem binders are baked into the surrounding term's expected type.
-- Workaround: write the def's type as a Π and `intro` all binders at
-- the start of the `by` block.

-- ============================================================
-- Toy demo: an extra hypothesis `h2 : Nat.le n n` whose type depends
-- on the index `n` of `h1 : Nat.le m n`.  The auto-revert pulls h2
-- back into G before the recursor is built, so in each branch h2's
-- type is correctly specialised.  No manual `revert h2` needed.
-- ============================================================

def Nat.le_dep_test : (m : Nat) -> (n : Nat) ->
    Nat.le m n -> Nat.le n n -> Nat :=
  by intro m; intro n; intro h1; intro h2;
     induction h1;
     -- refl branch: motive specialised to k=m, refl.  h2's specialised
     -- type is `Nat.le m m`.
     intro h2; exact 0;
     -- step branch: motive specialised to k=succ m1, step m m1 h_inner.
     -- h2's specialised type is `Nat.le (succ m1) (succ m1)`.
     intro m1; intro h_inner; intro ih; intro h2;
     exact 0

example : Eq.{1} Nat
    (Nat.le_dep_test 0 0 (Nat.le.refl 0) (Nat.le.refl 0)) 0 :=
  Eq.refl.{1} Nat 0

example : Eq.{1} Nat
    (Nat.le_dep_test 0 1
       (Nat.le.step 0 0 (Nat.le.refl 0))
       (Nat.le.refl 1))
    0 :=
  Eq.refl.{1} Nat 0

-- ============================================================
-- Transitive auto-revert: h3 depends on h2 depends on n.  Both get
-- reverted; the user intros them back in the original order.
-- ============================================================

def Nat.le_dep_chain : (m : Nat) -> (n : Nat) ->
    Nat.le m n -> Nat.le n n -> Nat.le n n -> Nat :=
  by intro m; intro n; intro h1; intro h2; intro h3;
     induction h1;
     -- refl: both h2 and h3 specialise to `Nat.le m m`.
     intro h2; intro h3; exact 1;
     -- step: both specialise to `Nat.le (succ m1) (succ m1)`.
     intro m1; intro h_inner; intro ih; intro h2; intro h3;
     exact 2

example : Eq.{1} Nat
    (Nat.le_dep_chain 0 0 (Nat.le.refl 0)
                          (Nat.le.refl 0) (Nat.le.refl 0))
    1 := Eq.refl.{1} Nat 1
