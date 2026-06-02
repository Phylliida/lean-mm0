"""Driver: validate the inductive generator against hand-written Nat, then
generate Bool + ListNat, and certify recursor computations over them.
Checked by mm0-rs AND mm0-c."""
import subprocess, os
import db_cert
from db_cert import (T, Var, App, Lam, Const, ESort, EPi, pp, prove_norm,
                     proof_nodes, TNAT, TZERO, TSUCC)
import induct
from induct import NAT, BOOL, LNAT, LIST, EQ, VEC

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
    expected = EPi(ESort("v"), EPi(C_kind, EPi(mnil, EPi(mcons, tail))))  # A : Sort v (poly)
    ok = LIST.rec_type == expected
    print(f"  List recursor-type regeneration matches hand-built: {ok}")
    if not ok:
        print("   expected:", pp(expected))
        print("   got     :", pp(LIST.rec_type))
    assert ok, "generator disagrees with hand-built List -- parametric de Bruijn bug"


def validate_eq():
    """Indexed inductive Eq.  Check the simple schemas (type former + ctor)
    against hand-built de Bruijn; the recursor type is validated end-to-end by
    mm0-c accepting the certified J-computation below (a wrong rec type would
    make prove_rec_partial_gen emit a proof mm0-rs rejects)."""
    induct._build(EQ)
    Sv = ESort("v")                     # A : Sort v -- Eq is now UNIVERSE-POLYMORPHIC
    S0 = ESort("lz")                    # Prop -- Eq's result sort (Eq : .. -> Prop)
    TEQ = Const("teq")
    def teq3(a, b, c): return App(App(App(TEQ, a), b), c)
    # teq : Pi A:Sort v, Pi a:A, Pi b:A, Prop
    tycon_exp = EPi(Sv, EPi(Var(0), EPi(Var(1), S0)))
    # refl : Pi A:Sort v, Pi a:A, teq A a a
    refl_exp = EPi(Sv, EPi(Var(0), teq3(Var(1), Var(0), Var(0))))
    ok1 = EQ.tycon_type == tycon_exp
    ok2 = EQ.ctor_types["refl_eq"] == refl_exp
    print(f"  Eq type-former matches hand-built:  {ok1}")
    print(f"  Eq refl ctor matches hand-built:    {ok2}")
    if not ok1: print("   got:", pp(EQ.tycon_type))
    if not ok2: print("   got:", pp(EQ.ctor_types['refl_eq']))
    assert ok1 and ok2, "Eq schema disagrees with hand-built -- indexed bug"


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

    # ---- indexed inductive Eq: the J eliminator computes on refl ----
    # eqrec A a C cr b h  with  b:=a, h:=refl A a   reduces to  cr.
    # Motive (non-dependent here):  C = \b:Nat. \h:(teq Nat 0 b). Nat.
    motive = Lam(TNAT, Lam(App(App(App(C("teq"), TNAT), TZERO), Var(0)), TNAT))
    refl0  = App(App(C("refl_eq"), TNAT), TZERO)         # refl : teq Nat 0 0
    jrule  = db_cert.curry(C("eqrec"),
        [TNAT, TZERO, motive, numeral(1), TZERO, refl0])
    yield ("J on refl: eqrec Nat 0 C 1 0 (refl Nat 0) = 1", jrule, numeral(1))

    # ---- RECURSIVE + INDEXED: Vec.  vlength extracts the length index. ----
    #   vrec A C m0 m1 : Pi n, Pi x:Vec A n, C n x.   Motive C = \n.\_. Nat.
    #   m0 (vnil)  = 0;   m1 n a xs ih = succ ih.
    def vec(A, *xs):                        # Vec A k literal for k = len(xs)
        t = App(C("vnil"), A)
        for i, x in enumerate(reversed(xs)):
            k = i                           # tail length so far
            t = db_cert.curry(C("vcons"), [A, numeral(k), x, t])
        return t
    def vlength(A):                         # : Pi n, Vec A n -> Nat
        Cmot = Lam(TNAT, Lam(App(App(C("tvec"), A), Var(0)), TNAT))  # \n.\_. Nat
        m0   = TZERO
        m1   = Lam(TNAT, Lam(A, Lam(App(App(C("tvec"), A), Var(1)),
                     Lam(TNAT, App(TSUCC, Var(0))))))   # \n a xs ih. succ ih
        return db_cert.curry(C("vrec"), [A, Cmot, m0, m1])
    # vlength Nat 2 [7,7] = 2   (apply at the major's index n=2 then the vector)
    v2 = vec(TNAT, numeral(7), numeral(7))
    call = App(App(vlength(TNAT), numeral(2)), v2)
    yield ("Vec (rec+indexed): vlength Nat [7,7] = 2", call, numeral(2))


def main():
    print("== validate generator ==")
    validate_nat()
    validate_list()
    validate_eq()

    print("\n== generate Bool + ListNat + List + Eq + Vec blocks ==")
    blocks = (induct.generate(BOOL) + "\n" + induct.generate(LNAT)
              + "\n" + induct.generate(LIST) + "\n" + induct.generate(EQ)
              + "\n" + induct.generate(VEC))
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


if __name__ == "__main__":
    main()


main()
