-- User-defined mixfix notation with bracket anchors.  Pattern is a
-- sequence of "string" literals (anchor tokens) and bare placeholder
-- ids, starting with a literal that acts as the trigger.  The
-- expansion is parsed once with placeholders as a bvar_stack; when
-- the notation fires, the captured argument exprs are substituted
-- in for the corresponding BVars.

-- ============================================================
-- Pair notation: `[a, b]` desugars to a Pair.mk call.
-- ============================================================

structure Pair.{u, v} (a : Sort u) (b : Sort v) : Sort (max u v) where
  (fst : a)
  (snd : b)

notation:1024 "[" a "," b "]" => Pair.mk.{1, 1} Nat Nat a b

def my_pair : Pair.{1, 1} Nat Nat := [3, 5]

example : Eq.{1} Nat (Pair.fst.{1, 1} Nat Nat my_pair) 3 := by rfl
example : Eq.{1} Nat (Pair.snd.{1, 1} Nat Nat my_pair) 5 := by rfl

-- ============================================================
-- Prefix unary: `!x` for `Not x`.  Single placeholder.
-- ============================================================

notation:1024 "!" x => Not x

example : Eq.{1} Prop (! True) (Not True) := Eq.refl.{1} Prop (Not True)

-- ============================================================
-- Singleton list: `<a>` desugars to `List.cons a List.nil`.
-- ============================================================

notation:1024 "<" a ">" => List.cons.{1} Nat a (List.nil.{1} Nat)

def my_one : List.{1} Nat := < 7 >

def list_length.{u} {a : Sort u} (xs : List.{u} a) : Nat :=
  match xs : Nat with
  | List.nil       => 0
  | List.cons h t  => Nat.succ (list_length t)

example : Eq.{1} Nat (@list_length.{1} Nat my_one) 1 := by rfl
