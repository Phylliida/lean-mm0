"""Per-feature demo: OPAQUE LEMMA REFERENCES -- modular proofs that scale.

A `theorem` is OPAQUE (the kernel never delta-unfolds it -- that is exactly how a
real proof chain stays cheap: each lemma is checked once, not re-normalised at every
call site).  The proof-term track now mirrors this: a cited lemma is emitted as an
mm0 def plus a `htop_<name> (g: ctx): ht g <body> <type>` theorem proved ONCE
(g-polymorphic, since a closed body's typing never pins the context), and every USE
types by REFERENCE to that theorem -- the body is never re-typed.

No trusted axiom: the lemma's typing is PROVED, not asserted (contrast a naive
`ht g L T` axiom, which would be unsound).  This is the stock-MM0 analogue of the
production verifier's opaque-def-typing rule, reached with the pieces already in
db.mm1.

Driven through the real proofterm_worker (parser -> elaborator -> kernel -> bridge
-> db_cert -> mm0-rs AND mm0-c).
"""
import os, re, sys, subprocess

HERE = os.path.dirname(os.path.abspath(__file__))

# zadd is a THEOREM (opaque); double_use cites it TWICE (via Eq.trans).  With true
# opacity the cited proof references zadd's typing rather than inlining it, so the
# proof of double_use is far smaller than two copies of zadd's induction proof.
SRC = r"""
theorem zadd (n : Nat) : Eq.{1} Nat (Nat.add 0 n) n :=
  @Nat.rec.{0}
    (fun (k : Nat) => Eq.{1} Nat (Nat.add 0 k) k)
    (Eq.refl.{1} Nat 0)
    (fun (k : Nat) (ih : Eq.{1} Nat (Nat.add 0 k) k) =>
       @Eq.rec.{1, 0} Nat (Nat.add 0 k)
         (fun (x : Nat) (_ : Eq.{1} Nat (Nat.add 0 k) x) =>
            Eq.{1} Nat (Nat.succ (Nat.add 0 k)) (Nat.succ x))
         (Eq.refl.{1} Nat (Nat.succ (Nat.add 0 k)))
         k ih)
    n
def double_use (n : Nat) : Eq.{1} Nat (Nat.add 0 (Nat.add 0 n)) n :=
  @Eq.trans.{1} Nat (Nat.add 0 (Nat.add 0 n)) (Nat.add 0 n) n
    (zadd (Nat.add 0 n))
    (zadd n)
"""


def nodes_of(mm1, thm):
    m = re.search(r"theorem %s[^=]*=\s*'(.*?);" % re.escape(thm), mm1, re.S)
    return len(re.findall(r"[A-Za-z_]\w*", m.group(1))) if m else None


def main():
    path = "/tmp/opaque_demo.lean"; open(path, "w").write(SRC)
    out = subprocess.run([sys.executable, f"{HERE}/proofterm_worker.py", path, "double_use"],
                         capture_output=True, text=True)
    line = next((l for l in out.stdout.splitlines() if l.startswith("RESULT ")), "")
    print(SRC.strip())
    print("\n" + (line or out.stdout + out.stderr))

    mm1path = "/tmp/pt_opaque_demo.lean_double_use.mm1"
    ok = "status=certified" in line
    if os.path.exists(mm1path):
        mm1 = open(mm1path).read()
        lemma = nodes_of(mm1, "htop_zadd")
        use = nodes_of(mm1, "pt")
        print(f"\n  lemma `zadd` typed ONCE (htop_zadd):        {lemma} nodes")
        print(f"  `double_use` proof (cites zadd x2, by ref): {use} nodes")
        if lemma:
            print(f"  inlining both copies would be ~{2*lemma}+ nodes "
                  f"-> opacity keeps the citing proof small.")

    print("\nopaque-lemma reference certified by BOTH checkers:", "OK" if ok else "FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
