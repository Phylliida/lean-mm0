"""Typed de-Bruijn demo: a `has_type` theorem whose proof routes a generated
reduction certificate through `ht_conv`.

We prove, for any motive cP : Nat -> Sort lu and any h : cP (add 1 1),
that  h : cP 2  -- which holds ONLY because (add 1 1) reduces to 2, and that
reduction is supplied as an explicit stock-MM0 certificate (no trusted
computation).  Checked by mm0-rs AND mm0-c."""
import subprocess, os
from db_cert import (Var, App, Lam, TNAT, TZERO, TSUCC, TREC,
                     curry, pp, prove_norm, prove_ht_nat, proof_nodes)

MM0   = "/home/bepis/prog/scientific-computing/mm0"
MM0RS = f"{MM0}/mm0-rs/target/release/mm0-rs"
MM0C  = f"{MM0}/mm0-c/mm0-c-np"
HERE  = os.path.dirname(os.path.abspath(__file__))

def num(n):
    t = TZERO
    for _ in range(n): t = App(TSUCC, t)
    return t

MOT = Lam(TNAT, TNAT)
SUC = Lam(TNAT, Lam(TNAT, App(TSUCC, Var(0))))
ADD = Lam(TNAT, Lam(TNAT, curry(TREC, [MOT, Var(1), SUC, Var(0)])))


def main():
    add11 = App(App(ADD, num(1)), num(1))
    nf, red = prove_norm(add11)                 # red : deq cnil (add 1 1) nf ;  nf == 2
    assert nf == num(2), pp(nf)
    h2 = prove_ht_nat(nf)                        # ht cnil 2 tnat

    # ht_conv : from  h : cP (add 1 1)  conclude  h : cP 2
    #   - reduction:  deq cnil (cP @ add11) (cP @ 2)   via congruence on `red`
    #   - well-typedness of the new type:  ht cnil (cP @ 2) (esort lu)
    proof = (f"(ht_conv hh "
             f"(deq_app (deq_refl) {red}) "
             f"(ht_app hP {h2} (sub_sort)))")
    thm = (f"-- AUTO-GENERATED: typed theorem via ht_conv + reduction certificate\n"
           f"theorem db_typed (lu: lvl) (cP h: expr)\n"
           f"  (hP: $ ht cnil cP (epi tnat (esort lu)) $)\n"
           f"  (hh: $ ht cnil h (cP @ {pp(add11)}) $):\n"
           f"  $ ht cnil h (cP @ {pp(nf)}) $ =\n'{proof};\n")

    open(f"{HERE}/_gen_db_typed.mm1", "w").write(thm)
    open("/tmp/cert_db_typed.mm1", "w").write(open(f"{HERE}/db.mm1").read() + "\n" + thm)

    print(thm)
    print("=" * 66)
    print(f"  reduction (add 1 1 => 2): {proof_nodes(red)} nodes")
    print(f"  full typed proof:         {proof_nodes(proof)} nodes")
    print("  this `h : cP 2` holds ONLY via the reduction -- ht_conv consumes it.")
    print("=" * 66)
    r = subprocess.run([MM0RS, "compile", "/tmp/cert_db_typed.mm1",
                        "/tmp/cert_db_typed.mmb"], capture_output=True, text=True)
    print("mm0-rs verify:", "OK (exit 0)" if r.returncode == 0 else "FAIL")
    if r.returncode != 0:
        print(r.stdout[-3000:]); print(r.stderr[-3000:]); return
    if os.path.exists(MM0C):
        rc = subprocess.run([MM0C, "/tmp/cert_db_typed.mmb"]).returncode
        print("mm0-c  verify:", "OK (exit 0)" if rc == 0 else f"FAIL ({rc})")


main()
