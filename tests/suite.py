"""Comprehensive test suite for the Lean → MM0 pipeline.

Each test is a (name, category, build, expected_status) tuple.
The runner exercises the pipeline end-to-end and reports
pass / fail / skip broken down by feature category.

`build` receives a fresh Env (with stdlib already loaded) and returns
a list of declaration names to emit and verify.
"""
from __future__ import annotations
import sys, os, io, traceback
from collections import defaultdict
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from src.levels import LZero, LSucc, LParam
from src.expr import (
    Sort, BVar, Const, App, Lam, Pi, Let, app_many, lam_many, pi_many,
)
from src.env import Env, Definition, Axiom
from src.kernel import Kernel, LocalCtx
from src.prelude_decls import build_stdlib, TYPE0, PROP
from src.emitter import emit_env
from src.mm0_verify import verify_file, verify_text


# ---------- builders ----------

def nat_lit(n: int):
    e = Const("Nat.zero", ())
    for _ in range(n):
        e = App(Const("Nat.succ", ()), e)
    return e


Nat = Const("Nat", ())
Bool = Const("Bool", ())


# ---------- individual test builders ----------
# Each `build_*` mutates `env` and returns a list of decl names to emit.

def b_id_function(env):
    # id.{u} : Π α : Sort u, α → α  :=  λ α x, x
    u = LParam("u")
    ty = Pi("α", Sort(u), Pi("x", BVar(0), BVar(1)))
    val = Lam("α", Sort(u), Lam("x", BVar(0), BVar(0)))
    env.add(Definition("id", ("u",), ty, val))
    return ["id"]


def b_id_application(env):
    b_id_function(env)
    # id_Nat_3 : Nat  :=  id.{1} Nat 3
    ty = Nat
    val = app_many(Const("id", (LSucc(LZero()),)), Nat, nat_lit(3))
    env.add(Definition("id_Nat_3", (), ty, val))
    return ["id", "id_Nat_3"]


def b_const_function(env):
    # const.{u,v} : Π α : Sort u, Π β : Sort v, α → β → α
    u = LParam("u"); v = LParam("v")
    ty = pi_many(
        ("α", Sort(u)),
        ("β", Sort(v)),
        ("x", BVar(1)),
        ("y", BVar(1)),
        BVar(3),
    )
    val = lam_many(
        ("α", Sort(u)),
        ("β", Sort(v)),
        ("x", BVar(1)),
        ("y", BVar(1)),
        BVar(1),
    )
    env.add(Definition("const_fn", ("u", "v"), ty, val))
    return ["const_fn"]


def b_nat_succ_two(env):
    # two : Nat := succ (succ zero)
    env.add(Definition("two", (), Nat, nat_lit(2)))
    return ["two"]


def b_nat_add_decl(env):
    # Nat.add is already in stdlib; emit it explicitly
    return ["Nat.add"]


def b_nat_add_application(env):
    # add_2_3 : Nat := Nat.add 2 3
    env.add(Definition(
        "add_2_3", (), Nat,
        app_many(Const("Nat.add", ()), nat_lit(2), nat_lit(3))))
    return ["Nat.add", "add_2_3"]


def b_nat_mul_decl(env):
    return ["Nat.add", "Nat.mul"]


def b_bool_const(env):
    env.add(Definition("my_true", (), Bool, Const("Bool.true", ())))
    return ["my_true"]


def b_list_nil(env):
    # empty_nats : List.{1} Nat := List.nil.{1} Nat
    ty = App(Const("List", (LSucc(LZero()),)), Nat)
    val = App(Const("List.nil", (LSucc(LZero()),)), Nat)
    env.add(Definition("empty_nats", (), ty, val))
    return ["empty_nats"]


def b_list_cons(env):
    # one_two : List Nat := cons 1 (cons 2 nil)
    ty = App(Const("List", (LSucc(LZero()),)), Nat)
    nil = App(Const("List.nil", (LSucc(LZero()),)), Nat)
    cons = lambda h, t: app_many(
        Const("List.cons", (LSucc(LZero()),)), Nat, h, t)
    val = cons(nat_lit(1), cons(nat_lit(2), nil))
    env.add(Definition("one_two", (), ty, val))
    return ["one_two"]


def b_and_intro(env):
    # tt_and_tt : And True True := And.intro True True True.intro True.intro
    True_ = Const("True", ())
    triv = Const("True.intro", ())
    ty = app_many(Const("And", ()), True_, True_)
    val = app_many(Const("And.intro", ()), True_, True_, triv, triv)
    env.add(Definition("tt_and_tt", (), ty, val))
    return ["tt_and_tt"]


def b_or_inl(env):
    True_ = Const("True", ())
    ty = app_many(Const("Or", ()), True_, True_)
    val = app_many(Const("Or.inl", ()), True_, True_, Const("True.intro", ()))
    env.add(Definition("tt_or_tt", (), ty, val))
    return ["tt_or_tt"]


def b_true_intro(env):
    env.add(Definition("triv", (), Const("True", ()), Const("True.intro", ())))
    return ["triv"]


def b_eq_refl_nat(env):
    # refl_3 : Eq Nat 3 3 := Eq.refl Nat 3
    ty = app_many(Const("Eq", (LSucc(LZero()),)), Nat, nat_lit(3), nat_lit(3))
    val = app_many(Const("Eq.refl", (LSucc(LZero()),)), Nat, nat_lit(3))
    env.add(Definition("refl_3", (), ty, val))
    return ["refl_3"]


def b_eq_refl_polymorphic(env):
    # refl_id.{u} : Π α : Sort u, Π x : α, Eq.{u} α x x  :=  Eq.refl
    u = LParam("u")
    ty = pi_many(
        ("α", Sort(u)),
        ("x", BVar(0)),
        app_many(Const("Eq", (u,)), BVar(1), BVar(0), BVar(0)),
    )
    val = lam_many(
        ("α", Sort(u)),
        ("x", BVar(0)),
        app_many(Const("Eq.refl", (u,)), BVar(1), BVar(0)),
    )
    env.add(Definition("refl_poly", ("u",), ty, val))
    return ["refl_poly"]


def b_let_binding(env):
    # let_six : Nat := let x : Nat := 3 in succ (succ (succ x))
    body = App(Const("Nat.succ", ()),
               App(Const("Nat.succ", ()),
                   App(Const("Nat.succ", ()), BVar(0))))
    val = Let("x", Nat, nat_lit(3), body)
    env.add(Definition("let_six", (), Nat, val))
    return ["let_six"]


def b_higher_order(env):
    # apply_twice : (Nat → Nat) → Nat → Nat  :=  λ f x, f (f x)
    arr = Pi("_", Nat, Nat)
    ty = Pi("f", arr, Pi("x", Nat, Nat))
    val = Lam("f", arr,
              Lam("x", Nat,
                  App(BVar(1), App(BVar(1), BVar(0)))))
    env.add(Definition("apply_twice", (), ty, val))
    return ["apply_twice"]


# ---- additional tests ----

def b_mutual_tree_forest(env):
    """Demonstrate mutual inductives (constructors only — no cross-recursor).
    Build a single Tree.node containing a Forest.cons of two Tree.leaf nodes."""
    from src.inductive import compile_mutual_inductives, InductiveSpec, CtorSpec, inductive_self
    compile_mutual_inductives(env, [
        InductiveSpec(
            name="Tree",
            level_params=(),
            params=(),
            sort=TYPE0,
            constructors=(
                CtorSpec(name="Tree.leaf", arg_types=()),
                CtorSpec(name="Tree.node", arg_types=(
                    ("f", Const("Forest", ())),
                )),
            ),
        ),
        InductiveSpec(
            name="Forest",
            level_params=(),
            params=(),
            sort=TYPE0,
            constructors=(
                CtorSpec(name="Forest.nil", arg_types=()),
                CtorSpec(name="Forest.cons", arg_types=(
                    ("t", Const("Tree", ())),
                    ("rest", inductive_self()),     # Forest
                )),
            ),
        ),
    ])
    # A small composite value
    leaf = Const("Tree.leaf", ())
    nil = Const("Forest.nil", ())
    inner = app_many(Const("Forest.cons", ()), leaf,
                     app_many(Const("Forest.cons", ()), leaf, nil))
    val = App(Const("Tree.node", ()), inner)
    env.add(Definition("my_tree", (), Const("Tree", ()), val))
    return ["my_tree"]


def b_subtype_mk(env):
    # A trivial subtype:  Subtype.{1} Nat (λ_. True)
    # mk : val=3, property=True.intro
    one = LSucc(LZero())
    triv_pred = Lam("_", Nat, Const("True", ()))
    ty = app_many(Const("Subtype", (one,)), Nat, triv_pred)
    val = app_many(Const("Subtype.mk", (one,)), Nat, triv_pred,
                   nat_lit(3), Const("True.intro", ()))
    env.add(Definition("triv_subtype", (), ty, val))
    return ["triv_subtype"]


def b_int_pos(env):
    val = App(Const("Int.ofNat", ()), nat_lit(7))
    env.add(Definition("int_seven", (), Const("Int", ()), val))
    return ["int_seven"]


def b_int_neg(env):
    # -3 = Int.negSucc 2
    val = App(Const("Int.negSucc", ()), nat_lit(2))
    env.add(Definition("int_neg_three", (), Const("Int", ()), val))
    return ["int_neg_three"]


def b_sigma_intro(env):
    # mk_dependent : Sigma.{1,1} Nat (λ_. Nat) := Sigma.mk Nat (λ_. Nat) 3 7
    one = LSucc(LZero())
    family = Lam("_", Nat, Nat)
    ty = app_many(Const("Sigma", (one, one)), Nat, family)
    val = app_many(Const("Sigma.mk", (one, one)), Nat, family, nat_lit(3), nat_lit(7))
    env.add(Definition("mk_dependent", (), ty, val))
    return ["mk_dependent"]


def b_prod_intro(env):
    # mk_nat_bool : Prod.{1,1} Nat Bool := Prod.mk Nat Bool 0 true
    ty = app_many(Const("Prod", (LSucc(LZero()), LSucc(LZero()))), Nat, Bool)
    val = app_many(Const("Prod.mk", (LSucc(LZero()), LSucc(LZero()))),
                   Nat, Bool, nat_lit(0), Const("Bool.true", ()))
    env.add(Definition("mk_nat_bool", (), ty, val))
    return ["mk_nat_bool"]


def b_sum_inl(env):
    ty = app_many(Const("Sum", (LSucc(LZero()), LSucc(LZero()))), Nat, Bool)
    val = app_many(Const("Sum.inl", (LSucc(LZero()), LSucc(LZero()))),
                   Nat, Bool, nat_lit(7))
    env.add(Definition("seven_or_bool", (), ty, val))
    return ["seven_or_bool"]


def b_option_none(env):
    ty = App(Const("Option", (LSucc(LZero()),)), Nat)
    val = App(Const("Option.none", (LSucc(LZero()),)), Nat)
    env.add(Definition("no_nat", (), ty, val))
    return ["no_nat"]


def b_option_some(env):
    ty = App(Const("Option", (LSucc(LZero()),)), Nat)
    val = app_many(Const("Option.some", (LSucc(LZero()),)), Nat, nat_lit(42))
    env.add(Definition("just_42", (), ty, val))
    return ["just_42"]


def b_implication(env):
    # tt_imp_tt : True → True  :=  λ _, True.intro
    True_ = Const("True", ())
    ty = Pi("_", True_, True_)
    val = Lam("_", True_, Const("True.intro", ()))
    env.add(Definition("tt_imp_tt", (), ty, val))
    return ["tt_imp_tt"]


def b_universal_quantifier(env):
    # refl_all : Π α : Type, Π x : α, Eq α x x  :=  λ α x, Eq.refl α x
    u_one = LSucc(LZero())
    ty = pi_many(
        ("α", TYPE0),
        ("x", BVar(0)),
        app_many(Const("Eq", (u_one,)), BVar(1), BVar(0), BVar(0)),
    )
    val = lam_many(
        ("α", TYPE0),
        ("x", BVar(0)),
        app_many(Const("Eq.refl", (u_one,)), BVar(1), BVar(0)),
    )
    env.add(Definition("refl_all_type", (), ty, val))
    return ["refl_all_type"]


def b_double_quantifier(env):
    # symmetric_pair_type : Π α : Type, α → α → Type
    #   λ α x y, Prod α α
    u_one = LSucc(LZero())
    ty = pi_many(("α", TYPE0), ("x", BVar(0)), ("y", BVar(1)), TYPE0)
    val = lam_many(("α", TYPE0), ("x", BVar(0)), ("y", BVar(1)),
                   app_many(Const("Prod", (u_one, u_one)), BVar(2), BVar(2)))
    env.add(Definition("pair_with_self", (), ty, val))
    return ["pair_with_self"]


def b_universe_zero_prop(env):
    # impl : Prop → Prop → Prop  :=  λ p q, Π _ : p, q
    arr = Pi("_", BVar(1), BVar(1))
    ty = Pi("p", PROP, Pi("q", PROP, PROP))
    val = Lam("p", PROP, Lam("q", PROP, arr))
    env.add(Definition("Impl", (), ty, val))
    return ["Impl"]


def b_polymorphic_id_at_type1(env):
    b_id_function(env)
    # id at Type:  Π α : Type, α → α  -- check we can instantiate at u=1
    ty = Pi("α", TYPE0, Pi("x", BVar(0), BVar(1)))
    val = App(Const("id", (LSucc(LZero()),)), Const("Nat", ()))
    # val : Nat → Nat ;  declared type as that
    decl_ty = Pi("_", Nat, Nat)
    env.add(Definition("id_at_Nat", (), decl_ty, val))
    return ["id", "id_at_Nat"]


def b_composition_application(env):
    b_composition(env)
    # apply compose to monomorphic types
    # compose_nat_nat_nat = compose.{1,1,1} Nat Nat Nat
    # type: (Nat → Nat) → (Nat → Nat) → (Nat → Nat)
    one = LSucc(LZero())
    arr = Pi("_", Nat, Nat)
    decl_ty = Pi("g", arr, Pi("f", arr, Pi("x", Nat, Nat)))
    val = app_many(Const("compose", (one, one, one)), Nat, Nat, Nat)
    env.add(Definition("compose_NNN", (), decl_ty, val))
    return ["compose", "compose_NNN"]


def b_curried_constant(env):
    b_const_function(env)
    # k_3_true : Nat → Bool → Nat  := const_fn.{1,1} Nat Bool ... wait, const_fn is
    # Π α β, α → β → α, so apply: const_fn.{1,1} Nat Bool : Nat → Bool → Nat
    one = LSucc(LZero())
    decl_ty = Pi("_", Nat, Pi("_", Bool, Nat))
    val = app_many(Const("const_fn", (one, one)), Nat, Bool)
    env.add(Definition("const_NB", (), decl_ty, val))
    return ["const_fn", "const_NB"]


def b_nested_let(env):
    # nested_let : Nat := let x := 1 in let y := 2 in succ (x)
    body_outer = Let("y", Nat, nat_lit(2),
                     App(Const("Nat.succ", ()), BVar(1)))     # uses outer x
    val = Let("x", Nat, nat_lit(1), body_outer)
    env.add(Definition("nested_let", (), Nat, val))
    return ["nested_let"]


def b_nat_pred(env):
    # Nat.pred : Nat → Nat := λ n, Nat.rec.{1} (λ _. Nat) 0 (λ k _. k) n
    one = LSucc(LZero())
    rec = app_many(
        Const("Nat.rec", (one,)),
        Lam("_", Nat, Nat),                              # motive
        Const("Nat.zero", ()),                            # base
        Lam("k", Nat, Lam("_ih", Nat, BVar(1))),         # step: ignore ih, return k
        BVar(0),                                          # major = n
    )
    val = Lam("n", Nat, rec)
    ty = Pi("n", Nat, Nat)
    env.add(Definition("Nat.pred", (), ty, val))
    return ["Nat.pred"]


def b_bool_not(env):
    # Bool.not : Bool → Bool := λ b, Bool.rec.{1} (λ _. Bool) true false b
    one = LSucc(LZero())
    rec = app_many(
        Const("Bool.rec", (one,)),
        Lam("_", Bool, Bool),
        Const("Bool.true", ()),                           # false ↦ true
        Const("Bool.false", ()),                          # true  ↦ false
        BVar(0),
    )
    val = Lam("b", Bool, rec)
    ty = Pi("b", Bool, Bool)
    env.add(Definition("Bool.not", (), ty, val))
    return ["Bool.not"]


def b_bool_and(env):
    # Bool.and : Bool → Bool → Bool := λ a b, Bool.rec.{1} (λ _. Bool) false b a
    one = LSucc(LZero())
    rec = app_many(
        Const("Bool.rec", (one,)),
        Lam("_", Bool, Bool),
        Const("Bool.false", ()),                          # a=false ⇒ false
        BVar(0),                                          # a=true  ⇒ b
        BVar(1),                                          # major  = a
    )
    val = Lam("a", Bool, Lam("b", Bool, rec))
    ty = Pi("a", Bool, Pi("b", Bool, Bool))
    env.add(Definition("Bool.and", (), ty, val))
    return ["Bool.and"]


def b_eq_subst(env):
    # Eq.subst.{u,v} : Π α : Sort u, Π P : α → Sort v, Π a b : α,
    #                  Eq.{u} α a b → P a → P b
    #   := λ α P a b h pa, Eq.rec.{u,v} α a
    #                        (λ b' _. P b')      -- motive (b':α, eq:Eq a b' )
    #                        pa
    #                        b h
    u, v = LParam("u"), LParam("v")
    α = Sort(u)
    eq_uv = lambda α_e, a_e, b_e: app_many(Const("Eq", (u,)), α_e, a_e, b_e)

    # Motive: λ b' : α, λ _ : Eq α a b', P b'
    # In context: α(BVar 5), P(4), a(3), b(2), h(1), pa(0) — outermost α
    # then we add motive's own binders b'(0) and _(1) inside it. So:
    # P is at BVar(4+2) = 6 inside motive body, and a is at BVar(3+2)=5.
    motive = Lam("b'", BVar(5),                          # α at depth 5+1? we're inside b' binder
                 Lam("_eq", eq_uv(BVar(6), BVar(4), BVar(0)),  # Eq α a b'
                     App(BVar(6), BVar(1))))             # P b'  (P at 4+2=6, b' at 1)
    val = lam_many(
        ("α", α),
        ("P", Pi("_", BVar(0), Sort(v))),
        ("a", BVar(1)),
        ("b", BVar(2)),
        ("h", eq_uv(BVar(3), BVar(1), BVar(0))),
        ("pa", App(BVar(3), BVar(2))),                   # P a
        app_many(
            Const("Eq.rec", (u, v)),
            BVar(5),                                      # α
            BVar(3),                                      # a
            motive,
            BVar(0),                                      # pa
            BVar(2),                                      # b
            BVar(1),                                      # h
        ),
    )
    ty = pi_many(
        ("α", α),
        ("P", Pi("_", BVar(0), Sort(v))),
        ("a", BVar(1)),
        ("b", BVar(2)),
        ("h", eq_uv(BVar(3), BVar(1), BVar(0))),
        ("pa", App(BVar(3), BVar(2))),
        App(BVar(4), BVar(2)),                            # P b
    )
    env.add(Definition("Eq.subst", ("u", "v"), ty, val))
    return ["Eq.subst"]


def b_eq_symm(env):
    # Eq.symm.{u} : Π α : Sort u, Π a b : α, Eq α a b → Eq α b a
    #   := λ α a b h, Eq.rec.{u, u} α a (λ b' _. Eq α b' a) (Eq.refl α a) b h
    u = LParam("u")
    α = Sort(u)
    eq_u = lambda α_e, x, y: app_many(Const("Eq", (u,)), α_e, x, y)
    # Stack at body position (lambdas: α, a, b, h):  h(0) b(1) a(2) α(3)
    # Motive: λ b' : α, λ _ : Eq α a b', Eq α b' a
    # Inside b' λ (stack: b'(0) h(1) b(2) a(3) α(4)):
    #   α=BVar(4), a=BVar(3)
    # Inside _eq λ (stack: _eq(0) b'(1) h(2) b(3) a(4) α(5)):
    #   motive body Eq α b' a = (BVar(5), BVar(1), BVar(4))
    motive = Lam("b'", BVar(3),                                # α
                 Lam("_eq", eq_u(BVar(4), BVar(3), BVar(0)),   # Eq α a b'
                     eq_u(BVar(5), BVar(1), BVar(4))))         # Eq α b' a
    val = lam_many(
        ("α", α),
        ("a", BVar(0)),
        ("b", BVar(1)),
        ("h", eq_u(BVar(2), BVar(1), BVar(0))),                # Eq α a b
        app_many(
            Const("Eq.rec", (u, LZero())),                      # motive lives in Prop
            BVar(3),                                            # α
            BVar(2),                                            # a
            motive,
            app_many(Const("Eq.refl", (u,)), BVar(3), BVar(2)), # Eq.refl α a : Eq α a a
            BVar(1),                                            # b
            BVar(0),                                            # h
        ),
    )
    ty = pi_many(
        ("α", α),
        ("a", BVar(0)),
        ("b", BVar(1)),
        ("h", eq_u(BVar(2), BVar(1), BVar(0))),
        eq_u(BVar(3), BVar(1), BVar(2)),                        # Eq α b a
    )
    env.add(Definition("Eq.symm", ("u",), ty, val))
    return ["Eq.symm"]


def b_apply_eq_symm(env):
    b_eq_symm(env)
    # symm_3_3 : Eq Nat 3 3 := Eq.symm.{1} Nat 3 3 (Eq.refl.{1} Nat 3)
    one = LSucc(LZero())
    refl33 = app_many(Const("Eq.refl", (one,)), Nat, nat_lit(3))
    val = app_many(Const("Eq.symm", (one,)), Nat, nat_lit(3), nat_lit(3), refl33)
    ty = app_many(Const("Eq", (one,)), Nat, nat_lit(3), nat_lit(3))
    env.add(Definition("symm_3_3", (), ty, val))
    return ["Eq.symm", "symm_3_3"]


def b_polymorphic_refl(env):
    # poly_refl.{u} : Π α : Sort u, Π x : α, Eq.{u} α x x
    u = LParam("u")
    α = Sort(u)
    ty = pi_many(
        ("α", α),
        ("x", BVar(0)),
        app_many(Const("Eq", (u,)), BVar(1), BVar(0), BVar(0)),
    )
    val = lam_many(
        ("α", α),
        ("x", BVar(0)),
        app_many(Const("Eq.refl", (u,)), BVar(1), BVar(0)),
    )
    env.add(Definition("poly_refl", ("u",), ty, val))
    return ["poly_refl"]


def b_nat_le_refl(env):
    # le_3_3 : Nat.le 3 3 := Nat.le.refl 3
    ty = app_many(Const("Nat.le", ()), nat_lit(3), nat_lit(3))
    val = App(Const("Nat.le.refl", ()), nat_lit(3))
    env.add(Definition("le_3_3", (), ty, val))
    return ["le_3_3"]


def b_nat_le_step(env):
    # le_3_4 : Nat.le 3 4 := Nat.le.step 3 3 (Nat.le.refl 3)
    ty = app_many(Const("Nat.le", ()), nat_lit(3), nat_lit(4))
    val = app_many(Const("Nat.le.step", ()), nat_lit(3), nat_lit(3),
                   App(Const("Nat.le.refl", ()), nat_lit(3)))
    env.add(Definition("le_3_4", (), ty, val))
    return ["le_3_4"]


def b_nat_le_chain(env):
    # le_3_5 : Nat.le 3 5 := step 3 4 (step 3 3 (refl 3))
    ty = app_many(Const("Nat.le", ()), nat_lit(3), nat_lit(5))
    inner = app_many(Const("Nat.le.step", ()), nat_lit(3), nat_lit(3),
                     App(Const("Nat.le.refl", ()), nat_lit(3)))
    val = app_many(Const("Nat.le.step", ()), nat_lit(3), nat_lit(4), inner)
    env.add(Definition("le_3_5", (), ty, val))
    return ["le_3_5"]


def b_quot_mk(env):
    # r : Nat → Nat → Prop := λ _ _. True
    Prop_ = PROP
    True_ = Const("True", ())
    r_ty = Pi("_", Nat, Pi("_", Nat, Prop_))
    r_val = Lam("_", Nat, Lam("_", Nat, True_))
    env.add(Definition("Nat.r_triv", (), r_ty, r_val))
    # mk_3 : Quot Nat Nat.r_triv := Quot.mk Nat Nat.r_triv 3
    one = LSucc(LZero())
    ty = app_many(Const("Quot", (one,)), Nat, Const("Nat.r_triv", ()))
    val = app_many(Const("Quot.mk", (one,)), Nat, Const("Nat.r_triv", ()), nat_lit(3))
    env.add(Definition("mk_3", (), ty, val))
    return ["Nat.r_triv", "mk_3"]


def b_quot_lift_compute(env):
    b_quot_mk(env)
    # const_zero : Nat → Nat := λ _. 0
    cz_ty = Pi("_", Nat, Nat)
    cz_val = Lam("_", Nat, Const("Nat.zero", ()))
    env.add(Definition("const_zero", (), cz_ty, cz_val))

    # h : Π a b, r a b → Eq Nat (const_zero a) (const_zero b)
    #   := λ a b _. Eq.refl Nat 0
    one = LSucc(LZero())
    eq1 = lambda α_e, x, y: app_many(Const("Eq", (one,)), α_e, x, y)
    # innermost (in λa,b,_):  Eq Nat 0 0 = Eq.refl Nat 0
    h_body = app_many(Const("Eq.refl", (one,)), Nat, Const("Nat.zero", ()))
    # under _ : r a b, body still Eq.refl Nat 0
    # build inside-out: (under λa, λb, λ_)
    h_inner = h_body
    # wrap _hab : r a b
    # stack outside _hab: b(0) a(1)
    h_inner = Lam("_hab", app_many(Const("Nat.r_triv", ()), BVar(1), BVar(0)), h_inner)
    h_inner = Lam("b", Nat, h_inner)
    h_inner = Lam("a", Nat, h_inner)
    # h's type
    h_ty_inner = eq1(Nat,
                     App(Const("const_zero", ()), BVar(2)),
                     App(Const("const_zero", ()), BVar(1)))
    h_ty = Pi("a", Nat,
              Pi("b", Nat,
                 Pi("_hab", app_many(Const("Nat.r_triv", ()), BVar(1), BVar(0)),
                    h_ty_inner)))
    env.add(Definition("const_zero_resp", (), h_ty, h_inner))

    # lift_via_quot : Nat
    #   := Quot.lift Nat r_triv Nat const_zero const_zero_resp (Quot.mk Nat r_triv 3)
    val = app_many(
        Const("Quot.lift", (one, one)),
        Nat,                                 # α
        Const("Nat.r_triv", ()),             # r
        Nat,                                 # β
        Const("const_zero", ()),             # f
        Const("const_zero_resp", ()),        # h
        app_many(Const("Quot.mk", (one,)), Nat,
                 Const("Nat.r_triv", ()), nat_lit(3)),
    )
    env.add(Definition("lift_via_quot", (), Nat, val))
    # And the computational claim:
    #   lift_via_quot_eq_0 : Eq Nat lift_via_quot 0  :=  Eq.refl Nat 0
    eq_ty = app_many(Const("Eq", (one,)), Nat,
                     Const("lift_via_quot", ()),
                     Const("Nat.zero", ()))
    eq_val = app_many(Const("Eq.refl", (one,)), Nat, Const("Nat.zero", ()))
    env.add(Definition("lift_via_quot_eq_0", (), eq_ty, eq_val))
    return ["Nat.r_triv", "mk_3", "const_zero", "const_zero_resp",
            "lift_via_quot", "lift_via_quot_eq_0"]


def b_vec_simple(env):
    # nil_at_Nat : Vec.{1} Nat 0 := Vec.nil.{1} Nat
    one = LSucc(LZero())
    ty = app_many(Const("Vec", (one,)), Nat, Const("Nat.zero", ()))
    val = App(Const("Vec.nil", (one,)), Nat)
    env.add(Definition("nil_at_Nat", (), ty, val))
    return ["nil_at_Nat"]


def b_vec_cons(env):
    # one_elem_vec : Vec.{1} Nat 1 := Vec.cons.{1} Nat 0 7 (Vec.nil Nat)
    one = LSucc(LZero())
    nil = App(Const("Vec.nil", (one,)), Nat)
    val = app_many(Const("Vec.cons", (one,)), Nat,
                   Const("Nat.zero", ()),     # n
                   nat_lit(7),                # a
                   nil)                        # t
    ty = app_many(Const("Vec", (one,)), Nat, nat_lit(1))
    env.add(Definition("one_elem_vec", (), ty, val))
    return ["one_elem_vec"]


def b_vec_length(env):
    # Vec.length.{u} : Π α : Sort u, Π n : Nat, Vec α n → Nat
    #   := λ α n v, Vec.rec.{u, 1} α (λ _ _. Nat) 0 (λ _ _ _ ih. succ ih) n v
    u = LParam("u")
    α_ty = Sort(u)
    # Body: stack (inside α, n, v lambdas): v(0) n(1) α(2)
    motive = Lam("_n", Nat, Lam("_v",
                                app_many(Const("Vec", (u,)), BVar(3), BVar(0)),
                                Nat))
    m_cons = Lam("_n", Nat,
                 Lam("_a", BVar(3),                                  # α
                     Lam("_t", app_many(Const("Vec", (u,)), BVar(4), BVar(1)),
                         Lam("ih", Nat,
                             App(Const("Nat.succ", ()), BVar(0))))))
    body = app_many(
        Const("Vec.rec", (u, LSucc(LZero()))),
        BVar(2),                                # α
        motive,                                  # motive
        Const("Nat.zero", ()),                   # m_nil = 0
        m_cons,                                  # m_cons
        BVar(1),                                 # n (index)
        BVar(0),                                 # v (major)
    )
    val = lam_many(
        ("α", α_ty),
        ("n", Nat),
        ("v", app_many(Const("Vec", (u,)), BVar(1), BVar(0))),
        body,
    )
    ty = pi_many(
        ("α", α_ty),
        ("n", Nat),
        ("v", app_many(Const("Vec", (u,)), BVar(1), BVar(0))),
        Nat,
    )
    env.add(Definition("Vec.length", ("u",), ty, val))
    return ["Vec.length"]


def b_vec_length_zero(env):
    b_vec_length(env)
    # length_nil_eq_0 : Eq Nat (Vec.length.{1} Nat 0 (Vec.nil Nat)) 0
    #                 := Eq.refl Nat 0
    one = LSucc(LZero())
    nil = App(Const("Vec.nil", (one,)), Nat)
    lhs = app_many(Const("Vec.length", (one,)), Nat, Const("Nat.zero", ()), nil)
    ty = app_many(Const("Eq", (one,)), Nat, lhs, Const("Nat.zero", ()))
    val = app_many(Const("Eq.refl", (one,)), Nat, Const("Nat.zero", ()))
    env.add(Definition("length_nil_eq_0", (), ty, val))
    return ["Vec.length", "length_nil_eq_0"]


def b_vec_length_two(env):
    b_vec_length(env)
    # length [7, 8] = 2
    one = LSucc(LZero())
    nil = App(Const("Vec.nil", (one,)), Nat)
    cons = lambda n_e, a, t: app_many(Const("Vec.cons", (one,)), Nat, n_e, a, t)
    v2 = cons(nat_lit(1), nat_lit(7), cons(nat_lit(0), nat_lit(8), nil))
    lhs = app_many(Const("Vec.length", (one,)), Nat, nat_lit(2), v2)
    ty = app_many(Const("Eq", (one,)), Nat, lhs, nat_lit(2))
    val = app_many(Const("Eq.refl", (one,)), Nat, nat_lit(2))
    env.add(Definition("length_two_elem_eq_2", (), ty, val))
    return ["Vec.length", "length_two_elem_eq_2"]


def b_add_2_3_eq_5(env):
    # The classic ι-computation test:
    #   add_2_3_eq_5 : Eq Nat (Nat.add 2 3) 5 := Eq.refl Nat 5
    # checks IFF the verifier reduces Nat.add 2 3 to 5 via β/δ/ι.
    one = LSucc(LZero())
    ty = app_many(Const("Eq", (one,)), Nat,
                  app_many(Const("Nat.add", ()), nat_lit(2), nat_lit(3)),
                  nat_lit(5))
    val = app_many(Const("Eq.refl", (one,)), Nat, nat_lit(5))
    env.add(Definition("add_2_3_eq_5", (), ty, val))
    return ["add_2_3_eq_5"]


def b_mul_2_3_eq_6(env):
    one = LSucc(LZero())
    ty = app_many(Const("Eq", (one,)), Nat,
                  app_many(Const("Nat.mul", ()), nat_lit(2), nat_lit(3)),
                  nat_lit(6))
    val = app_many(Const("Eq.refl", (one,)), Nat, nat_lit(6))
    env.add(Definition("mul_2_3_eq_6", (), ty, val))
    return ["mul_2_3_eq_6"]


def b_pred_5_eq_4(env):
    b_nat_pred(env)
    one = LSucc(LZero())
    ty = app_many(Const("Eq", (one,)), Nat,
                  App(Const("Nat.pred", ()), nat_lit(5)),
                  nat_lit(4))
    val = app_many(Const("Eq.refl", (one,)), Nat, nat_lit(4))
    env.add(Definition("pred_5_eq_4", (), ty, val))
    return ["Nat.pred", "pred_5_eq_4"]


def b_not_true_eq_false(env):
    b_bool_not(env)
    one = LSucc(LZero())
    ty = app_many(Const("Eq", (one,)), Bool,
                  App(Const("Bool.not", ()), Const("Bool.true", ())),
                  Const("Bool.false", ()))
    val = app_many(Const("Eq.refl", (one,)), Bool, Const("Bool.false", ()))
    env.add(Definition("not_true_eq_false", (), ty, val))
    return ["Bool.not", "not_true_eq_false"]


# ---- known-skip tests: document what the prototype does NOT yet handle ----

def b_iota_evaluation_skip(env):
    # Would express: prove (Eq Nat (Nat.add 2 3) 5) by Eq.refl.
    # Requires the verifier to fire ι reductions on Nat.rec so that the
    # definitional check (Nat.add 2 3) ≡ 5 succeeds.  Out of scope.
    raise NotImplementedError("ι-evaluation of recursors with recursive fields")


def b_vec_skip(env):
    # Vec.{u} : Type u → Nat → Type u   (indexed inductive)
    # Our inductive compiler does not yet handle indices.
    raise NotImplementedError("indexed inductives (Vec, Fin)")


def b_quotient_skip(env):
    # Quot.{u} : Π α : Sort u, (α → α → Prop) → Sort u
    # Quotient types are a primitive in Lean's kernel, not derived.
    raise NotImplementedError("quotient types")


def b_let_with_function(env):
    # let f := λ x, succ x in f (f 0)
    f_ty = Pi("_", Nat, Nat)
    f_val = Lam("x", Nat, App(Const("Nat.succ", ()), BVar(0)))
    body = App(BVar(0), App(BVar(0), nat_lit(0)))
    val = Let("f", f_ty, f_val, body)
    env.add(Definition("let_succ_twice", (), Nat, val))
    return ["let_succ_twice"]


def b_composition(env):
    # compose.{u,v,w} : Π α β γ, (β → γ) → (α → β) → (α → γ)
    # In the innermost body (stack: x f g γ β α from BVar 0..5):
    #   γ = BVar(3),  β = BVar(4),  α = BVar(5)
    u, v, w = LParam("u"), LParam("v"), LParam("w")
    ty = pi_many(
        ("α", Sort(u)), ("β", Sort(v)), ("γ", Sort(w)),
        ("g", Pi("_", BVar(1), BVar(1))),       # β → γ
        ("f", Pi("_", BVar(3), BVar(3))),       # α → β
        ("x", BVar(4)),                          # α
        BVar(3),                                  # γ
    )
    val = lam_many(
        ("α", Sort(u)), ("β", Sort(v)), ("γ", Sort(w)),
        ("g", Pi("_", BVar(1), BVar(1))),
        ("f", Pi("_", BVar(3), BVar(3))),
        ("x", BVar(4)),
        App(BVar(2), App(BVar(1), BVar(0))),
    )
    env.add(Definition("compose", ("u", "v", "w"), ty, val))
    return ["compose"]


# ---------- test registry ----------

TESTS = [
    # (name, category, builder, expected_status, note)
    ("True_intro",          "propositional", b_true_intro,            "pass", ""),
    ("And_intro",           "propositional", b_and_intro,             "pass", ""),
    ("Or_inl",              "propositional", b_or_inl,                "pass", ""),

    ("Eq_refl_nat",         "equality",      b_eq_refl_nat,           "pass", ""),
    ("Eq_refl_polymorphic", "equality",      b_eq_refl_polymorphic,   "pass", ""),

    ("Nat_succ_two",        "naturals",      b_nat_succ_two,          "pass", ""),
    ("Nat_add_decl",        "naturals",      b_nat_add_decl,          "pass", ""),
    ("Nat_add_application", "naturals",      b_nat_add_application,   "pass", ""),
    ("Nat_mul_decl",        "naturals",      b_nat_mul_decl,          "pass", ""),
    ("Bool_const",          "naturals",      b_bool_const,            "pass", ""),

    ("List_nil",            "polymorphic",   b_list_nil,              "pass", ""),
    ("List_cons",           "polymorphic",   b_list_cons,             "pass", ""),
    ("id_function",         "polymorphic",   b_id_function,           "pass", ""),
    ("id_application",      "polymorphic",   b_id_application,        "pass", ""),
    ("const_function",      "polymorphic",   b_const_function,        "pass", ""),
    ("composition",         "polymorphic",   b_composition,           "pass", ""),

    ("let_binding",         "let-zeta",      b_let_binding,           "pass", ""),
    ("nested_let",          "let-zeta",      b_nested_let,            "pass", ""),
    ("let_with_function",   "let-zeta",      b_let_with_function,     "pass", ""),
    ("higher_order",        "higher-order",  b_higher_order,          "pass", ""),

    # Practical inductive types
    ("Sigma_intro",         "inductives",    b_sigma_intro,           "pass", "dependent pair"),
    ("Subtype_mk",          "inductives",    b_subtype_mk,            "pass", "{n : Nat // True}"),
    ("Mutual_tree_forest",  "inductives",    b_mutual_tree_forest,    "pass", "mutual Tree/Forest ctors"),
    ("Int_pos",             "inductives",    b_int_pos,               "pass", "Int.ofNat"),
    ("Int_neg",             "inductives",    b_int_neg,               "pass", "Int.negSucc"),
    ("Prod_intro",          "inductives",    b_prod_intro,            "pass", ""),
    ("Sum_inl",             "inductives",    b_sum_inl,               "pass", ""),
    ("Option_none",         "inductives",    b_option_none,           "pass", ""),
    ("Option_some",         "inductives",    b_option_some,           "pass", ""),

    # Predicate logic / quantifiers
    ("implication",         "predicate-logic", b_implication,         "pass", ""),
    ("forall_eq_refl",      "predicate-logic", b_universal_quantifier, "pass", ""),
    ("double_quantifier",   "predicate-logic", b_double_quantifier,   "pass", ""),
    ("Prop_impl_def",       "predicate-logic", b_universe_zero_prop,  "pass", ""),

    # Universe / polymorphism instantiation
    ("id_at_Nat",           "instantiation", b_polymorphic_id_at_type1, "pass", ""),
    ("compose_NNN",         "instantiation", b_composition_application, "pass", ""),
    ("curried_const",       "instantiation", b_curried_constant,        "pass", ""),

    # Recursor-based definitions
    ("Nat_pred",            "recursors",     b_nat_pred,              "pass", "Nat.rec for pred"),
    ("Bool_not",            "recursors",     b_bool_not,              "pass", "Bool.rec for not"),
    ("Bool_and",            "recursors",     b_bool_and,              "pass", "Bool.rec for and"),
    ("Eq_subst",            "recursors",     b_eq_subst,              "pass", "Eq.rec (substitution)"),
    ("Eq_symm",             "recursors",     b_eq_symm,               "pass", "Eq.rec (symmetry)"),
    ("apply_eq_symm",       "recursors",     b_apply_eq_symm,         "pass", "Eq.symm applied to Eq.refl"),
    ("polymorphic_refl",    "recursors",     b_polymorphic_refl,      "pass", "universe-polymorphic refl"),

    # Computation by reflexivity (requires ι in the verifier)
    ("add_2_3_eq_5",        "computation",   b_add_2_3_eq_5,          "pass", "Nat.add 2 3 = 5 by Eq.refl"),
    ("mul_2_3_eq_6",        "computation",   b_mul_2_3_eq_6,          "pass", "Nat.mul 2 3 = 6 by Eq.refl"),
    ("pred_5_eq_4",         "computation",   b_pred_5_eq_4,           "pass", "Nat.pred 5 = 4 by Eq.refl"),
    ("not_true_eq_false",   "computation",   b_not_true_eq_false,     "pass", "Bool.not true = false by Eq.refl"),

    # Indexed inductives (Vec — exercises ι with index templates)
    ("Vec_nil",             "indexed",       b_vec_simple,            "pass", ""),
    ("Vec_cons",            "indexed",       b_vec_cons,              "pass", ""),
    ("Vec_length_def",      "indexed",       b_vec_length,            "pass", "Vec.length via Vec.rec"),
    ("Vec_length_nil",      "indexed",       b_vec_length_zero,       "pass", "computes length [] = 0"),
    ("Vec_length_two",      "indexed",       b_vec_length_two,        "pass", "computes length [7,8] = 2"),

    # Quotient types (Lean kernel primitives)
    ("Quot_mk",             "quotients",     b_quot_mk,               "pass", ""),
    ("Quot_lift_compute",   "quotients",     b_quot_lift_compute,     "pass", "Quot.lift f h (Quot.mk r a) = f a"),

    # Indexed inductive Prop: Nat.le
    ("Nat_le_refl",         "indexed-prop",  b_nat_le_refl,           "pass", ""),
    ("Nat_le_step",         "indexed-prop",  b_nat_le_step,           "pass", ""),
    ("Nat_le_chain",        "indexed-prop",  b_nat_le_chain,          "pass", "3 ≤ 5 via two steps"),
]


# ---------- runner ----------

def run_one(name, builder):
    env = Env()
    build_stdlib(env)
    decls = builder(env)
    # also include any prelude decls that the test references
    needed = set(decls)
    # transitive: walk env to include dependencies in order
    emit_list = [d for d in env.order if d in needed or d in _closure(env, needed)]
    buf = io.StringIO()
    emit_env(env, buf, only=emit_list)
    venv = verify_file("prelude/cic.mm0")
    verify_text(buf.getvalue(), venv)
    return True


def _closure(env, names):
    """Compute the transitive set of declarations referenced by `names`."""
    from src.expr import (
        Sort, BVar, FVar, Const, App, Lam, Pi, Let,
    )
    seen = set(names)
    worklist = list(names)
    def collect(e, acc):
        if isinstance(e, Const):
            acc.add(e.name)
        elif isinstance(e, (App,)):
            collect(e.fn, acc); collect(e.arg, acc)
        elif isinstance(e, (Lam, Pi)):
            collect(e.dom, acc); collect(e.body, acc)
        elif isinstance(e, Let):
            collect(e.type_, acc); collect(e.value, acc); collect(e.body, acc)
    while worklist:
        n = worklist.pop()
        if not env.has(n): continue
        d = env.get(n)
        for attr in ("type_", "value"):
            v = getattr(d, attr, None)
            if v is not None:
                refs = set()
                collect(v, refs)
                for r in refs:
                    if r not in seen and env.has(r):
                        seen.add(r); worklist.append(r)
    return seen


def main():
    by_cat = defaultdict(list)
    for t in TESTS:
        by_cat[t[1]].append(t)

    total = passed = failed = skipped = 0
    failures = []

    print("=" * 70)
    print(f"{'TEST':45} {'CAT':16} {'RESULT':8}")
    print("=" * 70)

    for cat, ts in by_cat.items():
        for (name, category, builder, expected, note) in ts:
            total += 1
            if expected == "skip":
                skipped += 1
                print(f"{name:45} {category:16} SKIP")
                continue
            try:
                run_one(name, builder)
                passed += 1
                print(f"{name:45} {category:16} OK")
            except Exception as e:
                failed += 1
                print(f"{name:45} {category:16} FAIL")
                failures.append((name, e, traceback.format_exc()))

    print("=" * 70)
    print(f"Total: {total}    Passed: {passed}    Failed: {failed}    Skipped: {skipped}")
    print()

    cat_counts = defaultdict(lambda: [0, 0, 0])    # [pass, fail, skip]
    for (name, cat, _, expected, _) in TESTS:
        if expected == "skip":
            cat_counts[cat][2] += 1
        else:
            ok = not any(f[0] == name for f in failures)
            cat_counts[cat][0 if ok else 1] += 1
    print("Coverage by category:")
    print("-" * 50)
    for cat, (p, f, s) in sorted(cat_counts.items()):
        print(f"  {cat:18}  pass:{p:>2}  fail:{f:>2}  skip:{s:>2}")
    print()

    if failures:
        print("Failure details:")
        for name, e, tb in failures:
            print(f"--- {name} ---")
            print(tb)
    return 0 if failed == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
