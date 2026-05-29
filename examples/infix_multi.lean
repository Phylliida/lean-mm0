-- Multi-character infix operators.  The lexer's sym branch is now
-- greedy on the `+-*<>=!` char set, so any contiguous run lexes as
-- one sym token.  Users can register these via `infix`, `infixl`,
-- or `infixr` like any other operator.  The runs are interrupted by
-- `->`, `=>`, and `--` (so those keep their punc/comment semantics).

-- ============================================================
-- `++` for list append.  Right-associative at precedence 65 (matches
-- standard Lean).
-- ============================================================

def append.{u} {a : Sort u}
    (xs : List.{u} a) (ys : List.{u} a) : List.{u} a :=
  match xs : List.{u} a with
  | List.nil       => ys
  | List.cons h t  => List.cons.{u} a h (append t ys)

infixr:65 ++ append

def my_l1 : List.{1} Nat :=
  List.cons.{1} Nat 1 (List.cons.{1} Nat 2 (List.nil.{1} Nat))
def my_l2 : List.{1} Nat :=
  List.cons.{1} Nat 3 (List.cons.{1} Nat 4 (List.nil.{1} Nat))

def joined : List.{1} Nat := my_l1 ++ my_l2

-- Right-associative: a ++ b ++ c parses as a ++ (b ++ c).
def my_l3 : List.{1} Nat :=
  List.cons.{1} Nat 5 (List.nil.{1} Nat)
def joined3 : List.{1} Nat := my_l1 ++ my_l2 ++ my_l3

-- Sanity: length is preserved.
def length.{u} {a : Sort u} (xs : List.{u} a) : Nat :=
  match xs : Nat with
  | List.nil       => 0
  | List.cons h t  => Nat.succ (length t)

example : Eq.{1} Nat (length joined) 4 := by rfl
example : Eq.{1} Nat (length joined3) 5 := by rfl

-- ============================================================
-- `**` as an alternative for Nat.mul.  Left-associative at 70.
-- ============================================================

infixl:70 ** Nat.mul

example : Eq.{1} Nat (3 ** 4) 12 := by rfl
example : Eq.{1} Nat (2 ** 3 ** 5) 30 := by rfl
