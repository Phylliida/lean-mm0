-- `apply` tactic: peels off the function's binders, fresh metas for each;
-- unifies the function's return type with the goal.  Any explicit binders
-- whose metas remain unsolved become subgoals, filled in order by the
-- subsequent `;`-chained tactics.
--
-- `assumption` tactic: succeeds if some local hypothesis is def-equal
-- to the goal (walks innermost-first).

-- Polymorphic identity, proved entirely by assumption.
def id_assn.{u} {a : Sort u} : a -> a := by intro x; assumption
example : Eq.{1} Nat (@id_assn.{1} Nat 7) 7 := by rfl

-- `assumption` picks the innermost match: snd selects y.
def snd : Nat -> Nat -> Nat := by intro x; intro y; assumption
example : Eq.{1} Nat (snd 5 9) 9 := by rfl

-- `apply Eq.refl` — unification solves the only explicit arg.
example : Eq.{1} Nat 4 4 := by apply Eq.refl

-- `apply Eq.symm` peels {α}{a}{b} as implicits + one explicit `Eq a b`.
-- Unifying `Eq b a` with the reflexive goal pins a=b, leaving an `Eq _ _`
-- subgoal that `rfl` solves.
example : Eq.{1} Nat 4 4 := by apply Eq.symm; rfl

-- After `intro h`, the assumption is available to discharge apply's
-- single subgoal.
def from_eq.{u} {T : Sort u} (x y : T) : Eq.{u} T x y -> Eq.{u} T y x :=
  by intro h; apply Eq.symm; assumption

-- Multi-subgoal `apply`: Eq.trans needs the middle term.  Supplying
-- @Eq.trans.{1} Nat 3 3 3 leaves two explicit Eq subgoals.
example : Eq.{1} Nat 3 3 := by apply @Eq.trans.{1} Nat 3 3 3; rfl; rfl
