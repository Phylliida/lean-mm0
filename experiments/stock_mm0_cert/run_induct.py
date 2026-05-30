"""Driver: validate the inductive generator against hand-written Nat, then
generate Bool + ListNat, and certify recursor computations over them.
Checked by mm0-rs AND mm0-c."""
import subprocess, os
import db_cert
from db_cert import (T, Var, App, Lam, Const, ESort, EPi, pp, prove_norm,
                     proof_nodes, TNAT, TZERO, TSUCC)
import induct
from induct import NAT, BOOL, LNAT, LIST

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


def validate_list():
    """Generator must reproduce the hand-built polymorphic List recursor type:
       Pi A:Sort1. Pi C:(List A)->Sort u. C(nil A) ->
         (Pi h:A, Pi t:List A, C t -> C(cons A h t)) -> Pi x:List A, C x
    De-Bruijn indices below carefully account for EVERY binder in scope,
    including the *anonymous* minor binders (e.g. inside m_cons the binders
    are [A, C, m_nil], so head:A is evar 2, not evar 1)."""
    induct._build(LIST)
    TL, NIL, CONS = Const("tlist"), Const("pnil"), Const("pcons")
    def V(i): return Var(i)
    # stack [A]            : C : (List A) -> Sort u
    C_kind = EPi(App(TL, V(0)), ESort("u"))
    # stack [A, C]         : m_nil = C (nil A)
    mnil   = App(V(0), App(NIL, V(1)))
    # stack [A, C, m_nil]  : m_cons = Pi h:A, Pi t:List A, C t -> C (cons A h t)
    mcons  = EPi(V(2),                                  # h : A
             EPi(App(TL, V(3)),                         # t : List A
             EPi(App(V(3), V(0)),                       # ih : C t
                 App(V(4), App(App(App(CONS, V(5)), V(2)), V(1))))))  # C (cons A h t)
    # stack [A, C, m_nil, m_cons] : Pi x:List A, C x
    tail   = EPi(App(TL, V(3)), App(V(3), V(0)))
    expected = EPi(ESort("(lS lz)"), EPi(C_kind, EPi(mnil, EPi(mcons, tail))))
    ok = LIST.rec_type == expected
    print(f"  List recursor-type regeneration matches hand-built: {ok}")
    if not ok:
        print("   expected:", pp(expected))
        print("   got     :", pp(LIST.rec_type))
    assert ok, "generator disagrees with hand-built List -- parametric de Bruijn bug"


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

    # ---- polymorphic List: the SAME recursor at two different parameters ----
    def plst(A, *xs):                       # List A literal:  cons A x .. (nil A)
        t = App(C("pnil"), A)
        for x in reversed(xs):
            t = App(App(App(C("pcons"), A), x), t)
        return t
    def plength(A):                         # length : List A -> Nat
        return db_cert.curry(C("prec"),
            [A,                                                 # parameter
             Lam(App(C("tlist"), A), TNAT),                     # motive \_.Nat
             TZERO,                                             # nil  -> 0
             Lam(A, Lam(App(C("tlist"), A),                     # cons -> succ ih
                        Lam(TNAT, App(TSUCC, Var(0)))))])
    yield ("length (List Nat)  [0,0]   = 2",
           App(plength(TNAT), plst(TNAT, numeral(0), numeral(0))), numeral(2))
    yield ("length (List Bool) [tt]    = 1",
           App(plength(C("tbool")), plst(C("tbool"), C("btrue"))), numeral(1))


def main():
    print("== validate generator ==")
    validate_nat()
    validate_list()

    print("\n== generate Bool + ListNat + (polymorphic) List blocks ==")
    blocks = (induct.generate(BOOL) + "\n" + induct.generate(LNAT)
              + "\n" + induct.generate(LIST))
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
