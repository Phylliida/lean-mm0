"""Per-feature demo: FREE-VARIABLE de-refl obligations.

The bridge used to certify only *closed* `Eq A a b` goals (`deq cnil a b`).  This
demo certifies obligations with free variables in context -- theorems of the
shape `(x : T) ... -> Eq A lhs rhs` that hold by computation (what `Eq.refl` /
`by rfl` discharge) but whose sides mention the bound variables.  Such a goal
genuinely cannot be stated in `cnil`: a recursor's iota gate must type the
free-variable motive/case, and `ht g (evar i) T` is only provable when `g` holds
the binder.  So the obligation is stated in its REAL context
`ccons T_{n-1} (... (ccons T_0 cnil))` and the certifier threads that context
through whnf's iota gates (ht_var0 / ht_weak).

Driven through the ACTUAL worker (parser -> elaborator -> kernel -> bridge ->
db_cert -> mm0-rs AND mm0-c), not a hand-built subset: this writes a
self-contained `.lean` and runs `coverage_worker.py` on it.  The lemmas use only
`build_stdlib` (Nat.add / Nat.mul), so they elaborate standalone.
"""
import os, re, sys, subprocess

HERE = os.path.dirname(os.path.abspath(__file__))

# Self-contained free-variable rfl lemmas.  Each holds by computation:
#   add_zero  : Nat.add recurses on its 2nd arg -> add n 0 reduces to n        (1 var)
#   mul_zero  : Nat.mul recurses on its 2nd arg -> mul n 0 reduces to 0        (1 var)
#   mul_one   : mul n 1 = add n (mul n 0) = add n 0 = n                        (1 var)
#   add_succ  : add m (succ n) = succ (add m n)  -- TWO free vars (ht_var0 + ht_weak)
SRC = r"""
def add_zero (n : Nat) : Eq.{1} Nat (Nat.add n 0) n :=
  Eq.refl.{1} Nat n
def mul_zero (n : Nat) : Eq.{1} Nat (Nat.mul n 0) 0 :=
  Eq.refl.{1} Nat 0
def mul_one (n : Nat) : Eq.{1} Nat (Nat.mul n 1) n :=
  Eq.refl.{1} Nat n
def add_succ (m n : Nat) :
    Eq.{1} Nat (Nat.add m (Nat.succ n)) (Nat.succ (Nat.add m n)) :=
  Eq.refl.{1} Nat (Nat.succ (Nat.add m n))
"""


def main():
    path = "/tmp/freevar_lemmas.lean"
    open(path, "w").write(SRC)
    out = subprocess.run([sys.executable, f"{HERE}/coverage_worker.py", path],
                         capture_output=True, text=True)
    line = next((l for l in out.stdout.splitlines() if l.startswith("RESULT ")), "")
    print(SRC.strip())
    print("\n" + (line or out.stdout + out.stderr))

    def gi(k):
        m = re.search(r" %s=(-?\d+)" % k, line); return int(m.group(1)) if m else -999
    ok = (gi("obligs") == 4 and gi("certified") == 4 and gi("skipped") == 0
          and gi("rs_rc") == 0 and gi("cc_rc") == 0 and "faithful=True" in line)
    print("\nfree-variable obligations certified by BOTH checkers:",
          "OK" if ok else "FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
