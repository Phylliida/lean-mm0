"""Driver: validate the inductive generator against hand-written Nat, then
generate Bool + ListNat, and certify recursor computations over them.
Checked by mm0-rs AND mm0-c."""
import subprocess, os
import db_cert
from db_cert import (T, Var, App, Lam, Const, ESort, EPi, pp, prove_norm,
                     proof_nodes, TNAT, TZERO, TSUCC)
import induct
from induct import NAT, BOOL, LNAT

MM0   = "/home/bepis/prog/scientific-computing/mm0"
MM0RS = f"{MM0}/mm0-rs/target/release/mm0-rs"
MM0C  = f"{MM0}/mm0-c/mm0-c-np"
HERE  = os.path.dirname(os.path.abspath(__file__))


def validate_nat():
    """Generator must reproduce db.mm1's hand-written Nat recursor type."""
    induct._build(NAT)
    # hand-built expected (matches db.mm1's ht_rec, de Bruijn):
    minor_zero = App(Var(0), TZERO)
    minor_succ = EPi(TNAT, EPi(App(Var(2), Var(0)),
                              App(Var(3), App(TSUCC, Var(1)))))
    tail = EPi(TNAT, App(Var(3), Var(0)))
    expected = EPi(EPi(TNAT, ESort("u")),
                   EPi(minor_zero, EPi(minor_succ, tail)))
    ok = NAT.rec_type == expected
    print(f"  Nat recursor-type regeneration matches db.mm1: {ok}")
    if not ok:
        print("   expected:", pp(expected))
        print("   got     :", pp(NAT.rec_type))
    assert ok, "generator disagrees with hand-written Nat -- de Bruijn bug"


def C(name): return Const(name)

def demos():
    # ---- Bool: not ----
    notb = Lam(C("tbool"),
               db_cert.curry(C("brec"),
                   [Lam(C("tbool"), C("tbool")),   # motive \_.Bool
                    C("bfalse"), C("btrue"),       # true-case, false-case
                    Var(0)]))
    yield ("not true  = false", App(notb, C("btrue")),  C("bfalse"))
    yield ("not false = true",  App(notb, C("bfalse")), C("btrue"))

    # ---- ListNat: length ----
    def lst(*xs):
        t = C("lnil")
        for x in reversed(xs):
            t = App(App(C("lcons"), x), t)
        return t
    def numeral(n):
        t = TZERO
        for _ in range(n): t = App(TSUCC, t)
        return t
    length = db_cert.curry(C("lrec"),
        [Lam(C("tlnat"), TNAT),                                  # motive \_.Nat
         TZERO,                                                  # nil-case = 0
         Lam(TNAT, Lam(C("tlnat"), Lam(TNAT, App(TSUCC, Var(0)))))])  # cons: succ ih
    yield ("length [0]      = 1", App(length, lst(numeral(0))), numeral(1))
    yield ("length [0,0,0]  = 3",
           App(length, lst(numeral(0), numeral(0), numeral(0))), numeral(3))


def main():
    print("== validate generator ==")
    validate_nat()

    print("\n== generate Bool + ListNat blocks ==")
    blocks = induct.generate(BOOL) + "\n" + induct.generate(LNAT)
    prelude = open(f"{HERE}/db.mm1").read() + "\n" + blocks
    open(f"{HERE}/_gen_induct.mm1", "w").write(blocks)

    frag = ["-- AUTO-GENERATED: recursor computations over generated inductives"]
    summary = []
    for i, (desc, e, expect) in enumerate(demos()):
        nf, conv = prove_norm(e)
        assert nf == expect, f"{desc}: emitter got {pp(nf)}, want {pp(expect)}"
        conv = conv or "(deq_refl)"
        n = proof_nodes(conv)
        frag.append(f"-- {desc}   ({n} nodes)\n"
                    f"theorem ind_{i}: $ deq cnil {pp(e)} {pp(nf)} $ =\n'{conv};\n")
        summary.append((desc, n))
    fragtext = "\n".join(frag)
    open("/tmp/cert_induct.mm1", "w").write(prelude + "\n" + fragtext)

    print("\n== certify computations ==")
    for desc, n in summary:
        print(f"  {n:5d} nodes   {desc}")

    r = subprocess.run([MM0RS, "compile", "/tmp/cert_induct.mm1",
                        "/tmp/cert_induct.mmb"], capture_output=True, text=True)
    print("\nmm0-rs verify:", "OK (exit 0)" if r.returncode == 0 else "FAIL")
    if r.returncode != 0:
        print(r.stdout[-3500:]); print(r.stderr[-3500:]); return
    if os.path.exists(MM0C):
        rc = subprocess.run([MM0C, "/tmp/cert_induct.mmb"]).returncode
        print("mm0-c  verify:", "OK (exit 0)" if rc == 0 else f"FAIL ({rc})")


main()
