"""Per-feature demo: LEVEL-GENERIC (open-universe) de-refl obligations.

The bridge used to reject any `Sort u` with a free universe param `u`
(`unsup:level` / `unsup:u`), monomorphising only at concrete use-site levels.  Now
an OPEN level is rendered with its bound param name (`Sort u` -> `(esort lv_u)`) and
the worker binds it as a `(lv_u: lvl)` theorem binder -- so a universe-polymorphic
goal is certified GENERICALLY, once, over all `u`.

The key finding: this needs NO trusted-base change.  db.mm1's `ht_sort (g)(l: lvl)`
and `deq_refl (g)(e)` already bind a level metavariable, so the open level simply
becomes a universally-quantified theorem binder; the certificate is valid for every
instantiation.  This is the exact dual of the free-variable (term-context) work:
free variables in the LEVEL context.

Driven through the ACTUAL worker (parser -> elaborator -> kernel -> bridge ->
db_cert -> mm0-rs AND mm0-c).  The lemmas use only Sort / Eq / lambda, so they
elaborate standalone.
"""
import os, re, sys, subprocess

HERE = os.path.dirname(os.path.abspath(__file__))

# Level-generic rfl lemmas.  Each holds by computation, GENERICALLY over u (and v):
#   refl_gen   : x = x                         -- trivial refl, generic universe u
#   beta_gen   : (fun z => z) x = x            -- a real beta-step under generic u
#   const_beta : (fun w => x) y = x            -- beta discarding an arg of a DIFFERENT
#                                                 universe v  (two level binders)
SRC = r"""
def refl_gen.{u} (a : Sort u) (x : a) : Eq.{u} a x x :=
  Eq.refl.{u} a x
def beta_gen.{u} (a : Sort u) (x : a) : Eq.{u} a ((fun (z : a) => z) x) x :=
  Eq.refl.{u} a x
def const_beta.{u, v} (a : Sort u) (b : Sort v) (x : a) (y : b) :
    Eq.{u} a ((fun (w : b) => x) y) x :=
  Eq.refl.{u} a x
"""


def main():
    path = "/tmp/levelgen_lemmas.lean"
    open(path, "w").write(SRC)
    out = subprocess.run([sys.executable, f"{HERE}/coverage_worker.py", path],
                         capture_output=True, text=True)
    line = next((l for l in out.stdout.splitlines() if l.startswith("RESULT ")), "")
    print(SRC.strip())
    print("\n" + (line or out.stdout + out.stderr))

    # show the emitted generic theorems (level binders visible)
    try:
        mm1 = open("/tmp/cov_levelgen_lemmas.lean.mm1").read()
        print("\n--- emitted generic theorems (note the (lv_*: lvl) binders) ---")
        for m in re.findall(r"theorem cov_\d+[^=]*?: \$ deq .*? \$", mm1):
            print("  " + (m[:140] + (" ..." if len(m) > 140 else "")))
    except FileNotFoundError:
        pass

    def gi(k):
        m = re.search(r" %s=(-?\d+)" % k, line); return int(m.group(1)) if m else -999
    ok = (gi("obligs") == 3 and gi("certified") == 3 and gi("skipped") == 0
          and gi("rs_rc") == 0 and gi("cc_rc") == 0 and "faithful=True" in line)
    print("\nlevel-generic obligations certified by BOTH checkers:",
          "OK" if ok else "FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
