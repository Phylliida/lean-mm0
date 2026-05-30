"""Speed benchmark: trusted reduction-by-COMPUTATION (our Python verifier's
_normalize) vs trusted reduction-by-CERTIFICATE-CHECKING (stock mm0-c).

Shared workload: Church-numeral multiplication  mul C_n C_n  ==>  C_(n*n),
pure beta (both verifiers handle it; no prelude/inductives needed).

  - our side: src/mm0_verify._normalize computes the beta-normal form (this is
    what our trusted verifier does when checking a `de-refl` conversion).
  - stock side: db_cert.prove_norm GENERATES an explicit certificate (untrusted,
    Python), then mm0-c checks it (trusted, C, zero computation).

The honest comparison is "our _normalize" vs "mm0-c check": both are the
trusted checker doing its job.  The certificate-generation time is the cost
that MOVED out of the trusted base.
"""
import sys, os, time, subprocess

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))            # lean-mm0/
sys.path.insert(0, os.path.join(ROOT, "src"))
sys.setrecursionlimit(5_000_000)

import mm0_verify
from db_cert import T, Var, App, Lam, Const, TNAT, pp, prove_norm

MM0   = "/home/bepis/prog/scientific-computing/mm0"
MM0RS = f"{MM0}/mm0-rs/target/release/mm0-rs"
MM0C  = f"{MM0}/mm0-c/mm0-c-np"

# ---- Church numerals + multiplication, in db_cert de-Bruijn terms ----
def church(n):                       # \f.\x. f (f (... (f x)))   (dummy domain)
    body = Var(0)
    for _ in range(n):
        body = App(Var(1), body)
    return Lam(TNAT, Lam(TNAT, body))

MUL = Lam(TNAT, Lam(TNAT, Lam(TNAT, App(Var(2), App(Var(1), Var(0))))))   # \m n f. m (n f)

def compute(n):
    return App(App(MUL, church(n)), church(n))

# ---- convert db_cert term -> our verifier's s-expression ----
def nlit(i):
    return "nzero" if i == 0 else ["nsucc", nlit(i-1)]
def to_sexpr(t):
    if isinstance(t, Var):   return ["evar", nlit(t.i)]
    if isinstance(t, App):   return ["eapp", to_sexpr(t.f), to_sexpr(t.a)]
    if isinstance(t, Lam):   return ["elam", to_sexpr(t.ty), to_sexpr(t.body)]
    if isinstance(t, Const): return t.name
    raise TypeError(t)

def proof_nodes(p):
    import re
    return len(re.findall(r'[A-Za-z_]\w*', p))


def bench(ns):
    prelude = open(f"{HERE}/db.mm1").read()
    rows = []
    for n in ns:
        e = compute(n)
        expect = church(n * n)

        # --- our verifier: compute the normal form ---
        se = to_sexpr(e)
        env = mm0_verify.VerifierEnv()
        t0 = time.perf_counter()
        got = mm0_verify._normalize(se, env, fuel=10**9)
        t_ours = time.perf_counter() - t0
        assert got == to_sexpr(expect), f"our verifier wrong at n={n}"

        # --- stock: generate certificate (untrusted, Python) ---
        t0 = time.perf_counter()
        nf, conv = prove_norm(e)
        t_gen = time.perf_counter() - t0
        assert nf == expect, f"emitter wrong at n={n}"
        nodes = proof_nodes(conv)

        thm = f"theorem bench_{n}: $ deq cnil {pp(e)} {pp(nf)} $ =\n'{conv};\n"
        mm1 = f"/tmp/bench_{n}.mm1"; mmb = f"/tmp/bench_{n}.mmb"
        open(mm1, "w").write(prelude + "\n" + thm)
        r = subprocess.run([MM0RS, "compile", mm1, mmb], capture_output=True, text=True)
        assert r.returncode == 0, r.stdout + r.stderr
        mmb_bytes = os.path.getsize(mmb)

        # --- stock kernel (mm0-c) check time: best of 3 ---
        t_c = min(_time_run([MM0C, mmb]) for _ in range(3))

        rows.append((n, n*n, t_ours, t_gen, nodes, mmb_bytes, t_c))
        print(f"  n={n:3d}  C_{n*n}: ours={t_ours*1e3:8.1f}ms  gen={t_gen*1e3:8.1f}ms  "
              f"nodes={nodes:8d}  mmb={mmb_bytes:9d}B  mm0-c={t_c*1e3:7.2f}ms")
    return rows

def _time_run(cmd):
    t0 = time.perf_counter()
    rc = subprocess.run(cmd, capture_output=True).returncode
    assert rc == 0, cmd
    return time.perf_counter() - t0


if __name__ == "__main__":
    print("Church mul C_n C_n => C_(n^2)   [pure beta]\n")
    rows = bench([4, 8, 12, 16, 20, 24, 28, 32])
    print("\n=== our _normalize (compute) vs mm0-c (check certificate) ===")
    for n, sq, t_ours, t_gen, nodes, mmb, t_c in rows:
        speedup = t_ours / t_c if t_c else float('inf')
        print(f"  n={n:3d}: our verifier {t_ours*1e3:8.1f}ms   "
              f"mm0-c {t_c*1e3:7.2f}ms   -> mm0-c {speedup:6.1f}x faster to CHECK")
