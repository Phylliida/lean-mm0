"""Build a standard library inside the kernel.

Provides:
  * Nat with rec
  * Bool
  * List.{u}
  * And, Or, True, False
  * Eq (handled specially: it has one index)
  * helpers:  Nat.add, Nat.mul, List.append, ...
"""
from __future__ import annotations
from .levels import LZero, LSucc, LParam, level_succ, level_zero, level_max, level_imax
from .expr import (
    Expr, Sort, BVar, Const, App, Lam, Pi, Let, app_many, lam_many, pi_many,
)
from .env import (
    Env, Definition, Axiom, Constructor, Recursor, RecursorRule, Inductive,
)
from .inductive import (
    InductiveSpec, CtorSpec, inductive_self, compile_inductive,
)


def _S(n: int) -> Expr:
    """Type universe `Sort (n+1)` = `Type n`."""
    lvl = LZero()
    for _ in range(n + 1):
        lvl = LSucc(lvl)
    return Sort(lvl)


TYPE0 = _S(0)        # Sort 1 in Lean = Type 0
PROP = Sort(LZero()) # Sort 0


def build_stdlib(env: Env) -> None:
    # ---- Bool ----
    compile_inductive(env, InductiveSpec(
        name="Bool",
        level_params=(),
        params=(),
        sort=TYPE0,
        constructors=(
            CtorSpec(name="Bool.false", arg_types=()),
            CtorSpec(name="Bool.true",  arg_types=()),
        ),
    ))

    # ---- Nat ----
    compile_inductive(env, InductiveSpec(
        name="Nat",
        level_params=(),
        params=(),
        sort=TYPE0,
        constructors=(
            CtorSpec(name="Nat.zero", arg_types=()),
            CtorSpec(name="Nat.succ", arg_types=(("n", inductive_self()),)),
        ),
    ))

    # ---- List.{u} ----
    compile_inductive(env, InductiveSpec(
        name="List",
        level_params=("u",),
        params=(("α", Sort(LParam("u"))),),
        sort=Sort(LParam("u")),
        constructors=(
            CtorSpec(name="List.nil",  arg_types=()),
            CtorSpec(name="List.cons", arg_types=(
                ("a", BVar(0)),                       # α
                ("t", inductive_self()),
            )),
        ),
    ))

    # ---- And ----
    compile_inductive(env, InductiveSpec(
        name="And",
        level_params=(),
        params=(("p", PROP), ("q", PROP)),
        sort=PROP,
        constructors=(
            CtorSpec(name="And.intro", arg_types=(
                ("hp", BVar(1)),                     # p
                ("hq", BVar(1)),                     # q  (after hp binder, q is BVar(1))
            )),
        ),
    ))

    # ---- Or ----
    compile_inductive(env, InductiveSpec(
        name="Or",
        level_params=(),
        params=(("p", PROP), ("q", PROP)),
        sort=PROP,
        constructors=(
            CtorSpec(name="Or.inl", arg_types=(("h", BVar(1)),)),   # p
            CtorSpec(name="Or.inr", arg_types=(("h", BVar(0)),)),   # q
        ),
    ))

    # ---- False ----
    compile_inductive(env, InductiveSpec(
        name="False",
        level_params=(),
        params=(),
        sort=PROP,
        constructors=(),
    ))

    # ---- True ----
    compile_inductive(env, InductiveSpec(
        name="True",
        level_params=(),
        params=(),
        sort=PROP,
        constructors=(CtorSpec(name="True.intro", arg_types=()),),
    ))

    # ---- Eq: hand-built (it has an index) ----
    _build_eq(env)

    # ---- Vec: indexed inductive ----
    _build_vec(env)

    # ---- Quotient types: Lean kernel primitives ----
    _build_quot(env)

    # ---- Nat.le, an indexed-inductive Prop ----
    _build_nat_le(env)

    # ---- More practical inductives ----
    _build_extra_inductives(env)

    # ---- Nat operations: add, mul ----
    _build_nat_ops(env)

    # ---- Eq.symm, Eq.trans ----
    _build_eq_lemmas(env)


def _build_eq_lemmas(env: Env) -> None:
    """Add Eq.symm and Eq.trans, both built from Eq.rec."""
    u = LParam("u")
    α = Sort(u)
    eq_u = lambda α_e, x, y: app_many(Const("Eq", (u,)), α_e, x, y)

    # Eq.symm.{u} : Π α (a b : α), Eq α a b → Eq α b a
    #   := λ α a b h, Eq.rec.{u, 0} α a (λ b' _. Eq α b' a) (Eq.refl α a) b h
    motive_symm = Lam("b'", BVar(3),
                       Lam("_eq", eq_u(BVar(4), BVar(3), BVar(0)),
                           eq_u(BVar(5), BVar(1), BVar(4))))
    val_symm = lam_many(
        ("α", α),
        ("a", BVar(0)),
        ("b", BVar(1)),
        ("h", eq_u(BVar(2), BVar(1), BVar(0))),
        app_many(
            Const("Eq.rec", (u, LZero())),
            BVar(3), BVar(2), motive_symm,
            app_many(Const("Eq.refl", (u,)), BVar(3), BVar(2)),
            BVar(1), BVar(0),
        ),
    )
    ty_symm = pi_many(
        ("α", α),
        ("a", BVar(0)),
        ("b", BVar(1)),
        ("h", eq_u(BVar(2), BVar(1), BVar(0))),
        eq_u(BVar(3), BVar(1), BVar(2)),
    )
    env.add(Definition("Eq.symm", ("u",), ty_symm, val_symm))

    # Eq.trans.{u} : Π α (a b c : α), Eq α a b → Eq α b c → Eq α a c
    #   := λ α a b c h1 h2. Eq.rec.{u, 0} α b (λ w _. Eq α a w) h1 c h2
    # Layout (innermost out): h2(0) h1(1) c(2) b(3) a(4) α(5).
    # Motive: λ w : α, λ _ : Eq α b w, Eq α a w.
    #   Inside motive scope (after w then _eq): _eq(0) w(1) h2(2) h1(3) c(4) b(5) a(6) α(7).
    # Inside motive: _eq(0), w(1), h2(2), h1(3), c(4), b(5), a(6), α(7).
    # Motive body should be `Eq α a w` (NOT `Eq α b w`).
    motive_trans = Lam("w", BVar(5),
                       Lam("_eq", eq_u(BVar(6), BVar(4), BVar(0)),
                           eq_u(BVar(7), BVar(6), BVar(1))))
    val_trans = lam_many(
        ("α", α),
        ("a", BVar(0)),
        ("b", BVar(1)),
        ("c", BVar(2)),
        ("h1", eq_u(BVar(3), BVar(2), BVar(1))),
        ("h2", eq_u(BVar(4), BVar(2), BVar(1))),
        app_many(
            Const("Eq.rec", (u, LZero())),
            BVar(5),         # α
            BVar(3),         # b (start point of Eq.rec)
            motive_trans,
            BVar(1),         # h1 : Eq α a b — used as P b case
            BVar(2),         # c (the end)
            BVar(0),         # h2 : Eq α b c
        ),
    )
    ty_trans = pi_many(
        ("α", α),
        ("a", BVar(0)),
        ("b", BVar(1)),
        ("c", BVar(2)),
        ("h1", eq_u(BVar(3), BVar(2), BVar(1))),
        ("h2", eq_u(BVar(4), BVar(2), BVar(1))),
        eq_u(BVar(5), BVar(4), BVar(2)),
    )
    env.add(Definition("Eq.trans", ("u",), ty_trans, val_trans))


def _build_vec(env: Env) -> None:
    """
    inductive Vec.{u} (α : Type u) : Nat → Type u
      | nil  : Vec α 0
      | cons (n : Nat) (a : α) (t : Vec α n) : Vec α (succ n)

    Vec.{u} : Π α : Type u, Nat → Type u
    Vec.nil.{u} : Π α : Type u, Vec.{u} α 0
    Vec.cons.{u} : Π α : Type u, Π n : Nat, α → Vec α n → Vec α (succ n)
    Vec.rec.{u, v} :
      Π α : Type u,
      Π motive : (Π n : Nat, Vec α n → Sort v),
        motive 0 (Vec.nil α) →
        (Π n : Nat, Π a : α, Π t : Vec α n,
           motive n t → motive (succ n) (Vec.cons α n a t)) →
        Π n : Nat, Π v : Vec α n, motive n v

    ι rules:
      Vec.rec α motive mn mc 0 (Vec.nil α)            ⟶  mn
      Vec.rec α motive mn mc (succ n) (Vec.cons α n a t)
                                                       ⟶  mc n a t (Vec.rec α motive mn mc n t)
    """
    u = LParam("u")
    v = LParam("v")
    α_ty = Sort(u)
    Nat_e = Const("Nat", ())
    Zero = Const("Nat.zero", ())
    Succ = lambda x: App(Const("Nat.succ", ()), x)
    Vec_at = lambda α_e, n_e: app_many(Const("Vec", (u,)), α_e, n_e)

    # Vec : Π α : Sort u, Nat → Sort u
    vec_type = Pi("α", α_ty, Pi("_n", Nat_e, Sort(u)))
    env.add(Inductive(
        name="Vec",
        level_params=("u",),
        type_=vec_type,
        num_params=1,
        num_indices=1,
        constructor_names=("Vec.nil", "Vec.cons"),
        recursor_name="Vec.rec",
    ))

    # Vec.nil : Π α, Vec α 0
    nil_type = Pi("α", α_ty, Vec_at(BVar(0), Zero))
    env.add(Constructor(
        name="Vec.nil",
        level_params=("u",),
        type_=nil_type,
        inductive="Vec",
        index=0,
        num_params=1,
        num_fields=0,
    ))

    # Vec.cons : Π α, Π n, α → Vec α n → Vec α (succ n)
    cons_type = Pi("α", α_ty,
                   Pi("n", Nat_e,
                      Pi("a", BVar(1),                                  # α
                         Pi("t", Vec_at(BVar(2), BVar(1)),               # Vec α n
                            Vec_at(BVar(3), Succ(BVar(2)))))))           # Vec α (succ n)
    env.add(Constructor(
        name="Vec.cons",
        level_params=("u",),
        type_=cons_type,
        inductive="Vec",
        index=1,
        num_params=1,
        num_fields=3,
    ))

    # Vec.rec.{u,v}: build inside-out
    # outer: α, motive, m_nil, m_cons, n, vec
    # body  = motive n vec   (motive=BVar(4) inside body, n=BVar(1), vec=BVar(0))
    # actually layout from outermost: α(0) motive(1) m_nil(2) m_cons(3) n(4) vec(5)
    # inside vec body, stack innermost out: vec(0) n(1) m_cons(2) m_nil(3) motive(4) α(5)
    rec_body = App(App(BVar(4), BVar(1)), BVar(0))                       # motive n vec
    # wrap vec : Vec α n   (stack outside vec binder: n(0) m_cons(1) m_nil(2) motive(3) α(4))
    vec_type_inside = Vec_at(BVar(4), BVar(0))
    body = Pi("vec", vec_type_inside, rec_body)
    # wrap n : Nat
    body = Pi("n", Nat_e, body)
    # m_cons : Π n a t, motive n t → motive (succ n) (cons α n a t)
    # outside m_cons (binders: α, motive, m_nil): stack: m_nil(0) motive(1) α(2)
    # inside m_cons, build the inner Π chain:
    # n binder: outside its type, scope=mc context. n's type=Nat. add it.
    # then a:α — α is BVar(3) in this scope (after n added) = 3 + 1 = 4? let me redo carefully.
    # Build inside-out for m_cons type:
    #   innermost: motive (succ n) (cons α n a t)
    #     stack at innermost: tih(0) t(1) a(2) n(3) m_nil(4) motive(5) α(6)
    #     motive = BVar(5), succ_n = succ BVar(3), cons = (cons α n a t) = App App App App cons α[6] n[3] a[2] t[1]
    cons_app = app_many(Const("Vec.cons", (u,)), BVar(6), BVar(3), BVar(2), BVar(1))
    succ_n = Succ(BVar(3))
    motive_target = App(App(BVar(5), succ_n), cons_app)
    mc_body = motive_target
    # wrap tih (recursive-witness binder): tih : motive n t
    # at the wrap point (inside t binder but not tih), stack: t(0) a(1) n(2) m_nil(3) motive(4) α(5)
    # motive = BVar(4), n = BVar(2), t = BVar(0)
    mc_body = Pi("tih", App(App(BVar(4), BVar(2)), BVar(0)), mc_body)
    # wrap t : Vec α n
    # at wrap point (inside a binder, no t yet), stack: a(0) n(1) m_nil(2) motive(3) α(4)
    # α = BVar(4), n = BVar(1)
    mc_body = Pi("t", Vec_at(BVar(4), BVar(1)), mc_body)
    # wrap a : α
    # at wrap point (inside n, no a yet), stack: n(0) m_nil(1) motive(2) α(3)
    # α = BVar(3)
    mc_body = Pi("a", BVar(3), mc_body)
    # wrap n : Nat
    mc_body = Pi("n", Nat_e, mc_body)
    body = Pi("m_cons", mc_body, body)
    # m_nil : motive 0 (Vec.nil α)
    # outside m_nil (binders α, motive): stack: motive(0) α(1)
    # motive = BVar(0), α = BVar(1)
    m_nil_type = App(App(BVar(0), Zero), App(Const("Vec.nil", (u,)), BVar(1)))
    body = Pi("m_nil", m_nil_type, body)
    # motive : Π n : Nat, Vec α n → Sort v
    # outside motive (binder α): α = BVar(0)
    # inside motive: build Pi n:Nat, Vec α n → Sort v
    # inner: Sort v (no BVars)
    # wrap Vec α n binder ("_"): inside its body, n is at BVar(1) (after "_"), α is at BVar(2) (after _ and n)
    # but Sort v doesn't reference them. type "Vec α n": at this position (inside n binder), α = BVar(1), n = BVar(0)
    motive_inner = Pi("_", Vec_at(BVar(1), BVar(0)), Sort(v))
    motive_type = Pi("n", Nat_e, motive_inner)
    body = Pi("motive", motive_type, body)
    # wrap α : Sort u
    body = Pi("α", α_ty, body)

    # ι rules for Vec.rec
    # nil rule: env_subst = [α, motive, m_nil, m_cons] (n_params=1, n_motives=1, n_minors=2, fields=0, rec=0)
    # BVar(0)=m_cons, (1)=m_nil, (2)=motive, (3)=α
    # RHS for nil = m_nil = BVar(1)
    nil_rule = RecursorRule(
        ctor_name="Vec.nil",
        num_fields=0,
        num_rec_args=0,
        rhs_template=BVar(1),
        rec_arg_positions=(),
    )
    # cons rule: env_subst = [α, motive, m_nil, m_cons, n, a, t, rec_result]
    # Order: params(α) + motives(motive) + minors(m_nil, m_cons) + fields(n, a, t) + rec_results(rec_t)
    # BVar(0)=rec_t, (1)=t, (2)=a, (3)=n, (4)=m_cons, (5)=m_nil, (6)=motive, (7)=α
    # RHS = m_cons n a t rec_t = App App App App BVar(4) BVar(3) BVar(2) BVar(1) BVar(0)
    cons_rhs = app_many(BVar(4), BVar(3), BVar(2), BVar(1), BVar(0))
    # rec_index_templates: for rec_position 2 (field t : Vec α n), the
    # index used in the recursive call is n = field 0.
    # In env_subst-without-rec_results (size 7), field 0 (n) is at:
    #   total=7, position of n = n_params + n_motives + n_minors + 0 = 4
    #   BVar = total - 1 - pos = 7 - 1 - 4 = 2
    cons_rule = RecursorRule(
        ctor_name="Vec.cons",
        num_fields=3,
        num_rec_args=1,
        rhs_template=cons_rhs,
        rec_arg_positions=(2,),
        rec_index_templates=((BVar(2),),),    # single rec arg, single index = n
    )
    env.add(Recursor(
        name="Vec.rec",
        level_params=("u", "v"),
        type_=body,
        inductive="Vec",
        num_params=1,
        num_motives=1,
        num_minors=2,
        num_indices=1,
        motive_universe_param="v",
        rules=(nil_rule, cons_rule),
    ))


def _build_nat_le(env: Env) -> None:
    """
    inductive Nat.le (n : Nat) : Nat → Prop
      | refl : Nat.le n n
      | step (m : Nat) : Nat.le n m → Nat.le n (succ m)

    Nat.le        : Nat → Nat → Prop
    Nat.le.refl   : Π n, Nat.le n n
    Nat.le.step   : Π n m, Nat.le n m → Nat.le n (succ m)
    Nat.le.rec.{u}: Π n,
                    Π motive : (Π k, Nat.le n k → Sort u),
                       motive n (Nat.le.refl n) →
                       (Π m h, motive m h → motive (succ m) (Nat.le.step n m h)) →
                       Π k h, motive k h
    """
    Nat_e = Const("Nat", ())
    Succ = lambda x: App(Const("Nat.succ", ()), x)
    Prop_ = Sort(LZero())

    # Nat.le : Π n : Nat, Π _ : Nat, Prop
    le_type = Pi("n", Nat_e, Pi("_", Nat_e, Prop_))
    env.add(Inductive(
        name="Nat.le",
        level_params=(),
        type_=le_type,
        num_params=1,
        num_indices=1,
        constructor_names=("Nat.le.refl", "Nat.le.step"),
        recursor_name="Nat.le.rec",
    ))

    # Nat.le.refl : Π n, Nat.le n n
    refl_type = Pi("n", Nat_e,
                   app_many(Const("Nat.le", ()), BVar(0), BVar(0)))
    env.add(Constructor(
        name="Nat.le.refl", level_params=(), type_=refl_type,
        inductive="Nat.le", index=0, num_params=1, num_fields=0,
    ))

    # Nat.le.step : Π n m, Nat.le n m → Nat.le n (succ m)
    # outermost → innermost: n, m, h, result
    step_type = Pi("n", Nat_e,
                   Pi("m", Nat_e,
                      Pi("_h", app_many(Const("Nat.le", ()), BVar(1), BVar(0)),
                         app_many(Const("Nat.le", ()), BVar(2), Succ(BVar(1))))))
    env.add(Constructor(
        name="Nat.le.step", level_params=(), type_=step_type,
        inductive="Nat.le", index=1, num_params=1, num_fields=2,
    ))

    # Nat.le.rec.{u}
    u = LParam("u")
    # Build inside-out.
    # Final body: motive k h
    # Binder stack at body (outermost first):
    #   n, motive, m_refl, m_step, k, h
    # Inside body: h(0) k(1) m_step(2) m_refl(3) motive(4) n(5)
    rec_body = App(App(BVar(4), BVar(1)), BVar(0))
    # wrap h : Nat.le n k ; stack: k(0) m_step(1) m_refl(2) motive(3) n(4)
    h_ty = app_many(Const("Nat.le", ()), BVar(4), BVar(0))
    body = Pi("h", h_ty, rec_body)
    # wrap k : Nat
    body = Pi("k", Nat_e, body)
    # m_step : Π m h, motive m h → motive (succ m) (step n m h)
    # outside m_step (binders n, motive, m_refl): m_refl(0) motive(1) n(2)
    # innermost: motive (succ m) (step n m h)
    # under m, h, hih:  hih(0) h(1) m(2) m_refl(3) motive(4) n(5)
    step_target = App(App(BVar(4), Succ(BVar(2))),
                       app_many(Const("Nat.le.step", ()), BVar(5), BVar(2), BVar(1)))
    mc_body = step_target
    # wrap hih : motive m h ; stack outside hih: h(0) m(1) m_refl(2) motive(3) n(4)
    mc_body = Pi("_hih", App(App(BVar(3), BVar(1)), BVar(0)), mc_body)
    # wrap h : Nat.le n m ; stack outside h: m(0) m_refl(1) motive(2) n(3)
    mc_body = Pi("_h", app_many(Const("Nat.le", ()), BVar(3), BVar(0)), mc_body)
    # wrap m : Nat
    mc_body = Pi("m", Nat_e, mc_body)
    body = Pi("m_step", mc_body, body)
    # m_refl : motive n (Nat.le.refl n)
    # outside m_refl: motive(0) n(1)
    m_refl_type = App(App(BVar(0), BVar(1)),
                       App(Const("Nat.le.refl", ()), BVar(1)))
    body = Pi("m_refl", m_refl_type, body)
    # motive : Π k, Nat.le n k → Sort u
    # outside motive: n(0)
    motive_inner = Pi("_", app_many(Const("Nat.le", ()), BVar(1), BVar(0)),
                      Sort(u))
    motive_type = Pi("k", Nat_e, motive_inner)
    body = Pi("motive", motive_type, body)
    # wrap n
    body = Pi("n", Nat_e, body)

    # ι rules
    # refl: env_subst = [n, motive, m_refl, m_step].  RHS = m_refl = BVar(1).
    refl_rule = RecursorRule(
        ctor_name="Nat.le.refl",
        num_fields=0,
        num_rec_args=0,
        rhs_template=BVar(1),
        rec_arg_positions=(),
    )
    # step: env_subst (no rec_results yet) = [n, motive, m_refl, m_step, m, h]
    # BVar(0)=h, (1)=m, (2)=m_step, (3)=m_refl, (4)=motive, (5)=n
    # After adding rec_result, env_subst has 7 entries; shift up by 1.
    # RHS = m_step m h rec_result = App App App BVar(3) BVar(2) BVar(1) BVar(0)
    step_rhs = app_many(BVar(3), BVar(2), BVar(1), BVar(0))
    # rec_index_template for recursion on `h` (rec position 1):
    #   index for the recursive call = m = BVar(1) in env_no_rec
    step_rule = RecursorRule(
        ctor_name="Nat.le.step",
        num_fields=2,
        num_rec_args=1,
        rhs_template=step_rhs,
        rec_arg_positions=(1,),                 # h is field 1
        rec_index_templates=((BVar(1),),),      # index = m
    )

    env.add(Recursor(
        name="Nat.le.rec",
        level_params=("u",),
        type_=body,
        inductive="Nat.le",
        num_params=1,
        num_motives=1,
        num_minors=2,
        num_indices=1,
        motive_universe_param="u",
        rules=(refl_rule, step_rule),
    ))


def _build_quot(env: Env) -> None:
    """Lean's quotient types are kernel primitives — not derivable.

        constant Quot.{u}      : Π {α : Sort u}, (α → α → Prop) → Sort u
        constant Quot.mk.{u}   : Π {α : Sort u} (r : α → α → Prop), α → Quot r
        constant Quot.lift.{u,v} :
            Π {α : Sort u} {r : α → α → Prop} {β : Sort v},
              (f : α → β) → (∀ a b, r a b → f a = f b) → Quot r → β
        constant Quot.ind.{u}  :
            Π {α : Sort u} {r : α → α → Prop} {motive : Quot r → Prop},
              (∀ a, motive (Quot.mk r a)) → ∀ q, motive q
        axiom    Quot.sound.{u}:
            Π {α : Sort u} {r : α → α → Prop} {a b : α},
              r a b → Quot.mk r a = Quot.mk r b

        ι-rule:  Quot.lift α r β f h (Quot.mk r a)  ⟶  f a
        ι-rule:  Quot.ind  α r m   m  (Quot.mk r a) ⟶  m a
    """
    u, v = LParam("u"), LParam("v")
    α_ty = Sort(u)
    Prop_ = Sort(LZero())
    rel_ty = lambda α_e: Pi("_", α_e, Pi("_", BVar(1), Prop_))  # α → α → Prop

    # Quot.{u} : Π α : Sort u, (α → α → Prop) → Sort u
    quot_type = Pi("α", α_ty,
                   Pi("r", rel_ty(BVar(0)),
                      Sort(u)))
    env.add(Inductive(
        name="Quot",
        level_params=("u",),
        type_=quot_type,
        num_params=2,            # α, r are both params
        num_indices=0,
        constructor_names=("Quot.mk",),
        recursor_name="Quot.lift",
    ))

    # Quot.mk.{u} : Π α, Π r, α → Quot α r
    mk_type = Pi("α", α_ty,
                 Pi("r", rel_ty(BVar(0)),
                    Pi("a", BVar(1),
                       app_many(Const("Quot", (u,)), BVar(2), BVar(1)))))
    env.add(Constructor(
        name="Quot.mk",
        level_params=("u",),
        type_=mk_type,
        inductive="Quot",
        index=0,
        num_params=2,
        num_fields=1,
    ))

    # Quot.lift.{u, v} : Π α, Π r, Π β : Sort v,
    #     (α → β) → (Π a b : α, r a b → Eq β (f a) (f b)) → Quot r → β
    # We use a relaxed form (omitting the h condition's exact shape, only
    # requiring the right *type*) — the encoded type still type-checks.
    β_ty = Sort(v)
    eq_v = lambda β_e, x_e, y_e: app_many(Const("Eq", (v,)), β_e, x_e, y_e)
    # build inside-out for clarity
    # Innermost binders (outer→inner): α(0) r(1) β(2) f(3) h(4) q(5), body = β
    # Body uses β at BVar(3).
    body = BVar(3)
    # wrap q : Quot r ; stack outside q: h(0) f(1) β(2) r(3) α(4)
    q_ty = app_many(Const("Quot", (u,)), BVar(4), BVar(3))
    body = Pi("q", q_ty, body)
    # wrap h : Π a b, r a b → Eq β (f a) (f b)
    # at h's type position, stack: f(0) β(1) r(2) α(3)
    # build the h type inside-out
    # innermost (under a, b, hab): hab(0) b(1) a(2) f(3) β(4) r(5) α(6)
    h_innermost = eq_v(BVar(4), App(BVar(3), BVar(2)), App(BVar(3), BVar(1)))
    # wrap hab : r a b  ; outside hab: b(0) a(1) f(2) β(3) r(4) α(5)
    h_ty = Pi("_hab", app_many(BVar(4), BVar(1), BVar(0)), h_innermost)
    # wrap b : α  ; outside b: a(0) f(1) β(2) r(3) α(4)
    h_ty = Pi("b", BVar(4), h_ty)
    # wrap a : α
    h_ty = Pi("a", BVar(3), h_ty)
    body = Pi("h", h_ty, body)
    # wrap f : α → β ; outside f: β(0) r(1) α(2)
    f_ty = Pi("_", BVar(2), BVar(1))
    body = Pi("f", f_ty, body)
    # wrap β : Sort v
    body = Pi("β", β_ty, body)
    # wrap r : α → α → Prop
    body = Pi("r", rel_ty(BVar(0)), body)
    # wrap α : Sort u
    body = Pi("α", α_ty, body)

    env.add(Recursor(
        name="Quot.lift",
        level_params=("u", "v"),
        type_=body,
        inductive="Quot",
        num_params=3,            # α, r, β  (recursor's spine "params")
        num_motives=0,
        num_minors=2,            # f, h
        num_indices=0,
        motive_universe_param="v",
        # Iota: Quot.lift α r β f h (Quot.mk α r a) ⟶ f a
        # env_subst order:  [α, r, β, f, h, a]   (n_params + n_minors + n_fields)
        # BVar(0)=a, (1)=h, (2)=f, (3)=β, (4)=r, (5)=α
        # RHS = f a = App(BVar(2), BVar(0))
        rules=(RecursorRule(
            ctor_name="Quot.mk",
            num_fields=1,
            num_rec_args=0,
            rhs_template=App(BVar(2), BVar(0)),
            rec_arg_positions=(),
            n_ctor_params_override=2,                # Quot.mk has 2 params, not 3
        ),),
    ))

    # Quot.sound axiom
    # Π α : Sort u, Π r : α → α → Prop, Π a b : α, r a b → Eq.{u} (Quot r) (Quot.mk α r a) (Quot.mk α r b)
    eq_u = lambda α_e, x, y: app_many(Const("Eq", (u,)), α_e, x, y)
    sound_inner_eq = eq_u(
        app_many(Const("Quot", (u,)), BVar(3), BVar(2)),
        app_many(Const("Quot.mk", (u,)), BVar(3), BVar(2), BVar(1)),
        app_many(Const("Quot.mk", (u,)), BVar(3), BVar(2), BVar(0)),
    )
    # outermost → innermost: α(0) r(1) a(2) b(3) hab(4)
    # inside the body: 4 binders above hab... actually outside.
    sound_ty = Pi("α", α_ty,
                  Pi("r", rel_ty(BVar(0)),
                     Pi("a", BVar(1),
                        Pi("b", BVar(2),
                           Pi("_hab", app_many(BVar(2), BVar(1), BVar(0)),
                              sound_inner_eq)))))
    env.add(Axiom("Quot.sound", ("u",), sound_ty))


def _build_extra_inductives(env: Env) -> None:
    u, v = LParam("u"), LParam("v")

    # Sigma.{u,v} : Π α : Sort u, Π β : α → Sort v, Sort (max u v)
    # Sigma.mk α β (a : α) (b : β a) : Sigma α β
    compile_inductive(env, InductiveSpec(
        name="Sigma",
        level_params=("u", "v"),
        params=(
            ("α", Sort(u)),
            ("β", Pi("_", BVar(0), Sort(v))),         # α → Sort v
        ),
        sort=Sort(level_max(u, v)),
        constructors=(CtorSpec(name="Sigma.mk", arg_types=(
            ("a", BVar(1)),                           # α
            ("b", App(BVar(1), BVar(0))),             # β a
        )),),
    ))

    # Prod.{u,v} : Π α β, Type (max u v)
    compile_inductive(env, InductiveSpec(
        name="Prod",
        level_params=("u", "v"),
        params=(("α", Sort(u)), ("β", Sort(v))),
        sort=Sort(level_max(u, v)),
        constructors=(CtorSpec(name="Prod.mk", arg_types=(
            ("a", BVar(1)),               # α
            ("b", BVar(1)),               # β  (after a binder, β is BVar(1))
        )),),
    ))

    # Sum.{u,v} : Π α β, Type (max u v)
    compile_inductive(env, InductiveSpec(
        name="Sum",
        level_params=("u", "v"),
        params=(("α", Sort(u)), ("β", Sort(v))),
        sort=Sort(level_max(u, v)),
        constructors=(
            CtorSpec(name="Sum.inl", arg_types=(("a", BVar(1)),)),   # α
            CtorSpec(name="Sum.inr", arg_types=(("b", BVar(0)),)),   # β
        ),
    ))

    # Option.{u} : Π α, Type u
    compile_inductive(env, InductiveSpec(
        name="Option",
        level_params=("u",),
        params=(("α", Sort(u)),),
        sort=Sort(u),
        constructors=(
            CtorSpec(name="Option.none", arg_types=()),
            CtorSpec(name="Option.some", arg_types=(("a", BVar(0)),)),  # α
        ),
    ))

    # Empty : Type   (no constructors — used for proofs by contradiction at Type level)
    compile_inductive(env, InductiveSpec(
        name="Empty",
        level_params=(),
        params=(),
        sort=TYPE0,
        constructors=(),
    ))

    # Subtype.{u} : Π (α : Sort u) (p : α → Prop), Sort u
    # constructor: Subtype.mk (val : α) (property : p val)
    compile_inductive(env, InductiveSpec(
        name="Subtype",
        level_params=("u",),
        params=(
            ("α", Sort(u)),
            ("p", Pi("_", BVar(0), Sort(LZero()))),    # α → Prop
        ),
        sort=Sort(u),
        constructors=(CtorSpec(name="Subtype.mk", arg_types=(
            ("val", BVar(1)),                          # α
            ("property", App(BVar(1), BVar(0))),       # p val
        )),),
    ))

    # Int : Type   (encoded the same way Lean 4 encodes it)
    #   | ofNat   (n : Nat)      :  representing  n ≥ 0
    #   | negSucc (n : Nat)      :  representing  -(n+1)
    compile_inductive(env, InductiveSpec(
        name="Int",
        level_params=(),
        params=(),
        sort=TYPE0,
        constructors=(
            CtorSpec(name="Int.ofNat",   arg_types=(("n", Const("Nat", ())),)),
            CtorSpec(name="Int.negSucc", arg_types=(("n", Const("Nat", ())),)),
        ),
    ))


# ---------- Eq (indexed) ----------

def _build_eq(env: Env) -> None:
    """
    inductive Eq.{u} {α : Sort u} (a : α) : α → Prop
      | refl : Eq a a

    Eq.{u} : Π {α : Sort u}, α → α → Prop
    Eq.refl.{u} : Π {α : Sort u} (a : α), Eq.{u} α a a
    Eq.rec.{u, v} :
      Π {α : Sort u} {a : α} {motive : (b : α) → Eq.{u} α a b → Sort v},
        motive a (Eq.refl.{u} α a) →
        Π {b : α} (h : Eq.{u} α a b), motive b h
    Iota:
      Eq.rec α a motive m_refl a (Eq.refl α a)  →  m_refl
    """
    u = LParam("u")
    v = LParam("v")
    α = Sort(u)

    # Eq : Π α : Sort u, α → α → Prop
    eq_type = Pi("α", α,
                 Pi("a", BVar(0),
                    Pi("b", BVar(1),
                       Sort(LZero()))))
    env.add(Inductive(
        name="Eq",
        level_params=("u",),
        type_=eq_type,
        num_params=2,        # α and a count as "params" for the purpose of recursor
        num_indices=1,       # the b
        constructor_names=("Eq.refl",),
        recursor_name="Eq.rec",
    ))

    # Eq.refl : Π α, Π a, Eq.{u} α a a
    refl_type = Pi("α", α,
                   Pi("a", BVar(0),
                      app_many(Const("Eq", (u,)), BVar(1), BVar(0), BVar(0))))
    env.add(Constructor(
        name="Eq.refl",
        level_params=("u",),
        type_=refl_type,
        inductive="Eq",
        index=0,
        num_params=2,
        num_fields=0,
    ))

    # Eq.rec.{u,v} :
    #   Π α, Π a, Π motive : (Π b:α. Eq α a b → Sort v),
    #     Π m_refl : motive a (Eq.refl α a),
    #       Π b:α, Π h:Eq α a b, motive b h
    motive_type = Pi("b", α,
                     Pi("_", app_many(Const("Eq", (u,)), BVar(2), BVar(1), BVar(0)),
                        Sort(v)))
    # In context: outside motive sit α (BVar 0 from outside is α), a (BVar 1 outside).
    # We're building inside-out, so be careful with indices.
    # Layout from outermost:  α, a, motive, m_refl, b, h
    # When we write motive_type above, α is at BVar(?) seen from inside motive.
    # We'll re-construct with the correct depths inside `rec_type`.

    # Easier: build everything inside-out.
    # Innermost: motive applied to b and h.
    # Inside the body of `h`-binder: motive @ BVar(2) @ BVar(0)? No, let's lay out indices.
    #
    # Final body: `motive b h`
    # Binder stack outermost→innermost: α(0) a(1) motive(2) m_refl(3) b(4) h(5)
    # BVar(i) means "i binders up from current scope", so in the innermost
    # body BVar(0)=h, BVar(1)=b, BVar(2)=m_refl, BVar(3)=motive, BVar(4)=a, BVar(5)=α.
    # motive applied to b applied to h: App(App(motive, b), h) = App(App(BVar(3), BVar(1)), BVar(0))
    rec_body = App(App(BVar(3), BVar(1)), BVar(0))
    # wrap h : Eq α a b
    # inside the h-binder body (after this wrap), eq applied is: Eq.{u} α a b
    # at depth of "wrapping h", we're outside the h binder; indices for α,a,b
    # are α=BVar(4) a=BVar(3) b=BVar(0)?? Let's reason: after we wrap h, h becomes
    # BVar(0) for inner code. But the h's TYPE is computed at the moment just
    # before wrapping, where the surrounding scope has: α a motive m_refl b (no h yet).
    # So at the h-type position: α=BVar(4), a=BVar(3), motive=BVar(2), m_refl=BVar(1), b=BVar(0).
    h_type = app_many(Const("Eq", (u,)), BVar(4), BVar(3), BVar(0))
    body = Pi("h", h_type, rec_body)
    # wrap b : α; before wrapping b, scope has α a motive m_refl (4 things). α=BVar(3).
    body = Pi("b", BVar(3), body)
    # wrap m_refl : motive a (Eq.refl.{u} α a)
    # before wrapping m_refl, scope has α a motive (3 things).
    # α=BVar(2), a=BVar(1), motive=BVar(0).
    # motive applied to a and (Eq.refl α a)
    refl_a = app_many(Const("Eq.refl", (u,)), BVar(2), BVar(1))
    m_refl_type = App(App(BVar(0), BVar(1)), refl_a)
    body = Pi("m_refl", m_refl_type, body)
    # wrap motive : Π b:α, Eq α a b → Sort v
    # before wrapping motive, scope has α a (2 things). α=BVar(1), a=BVar(0).
    # motive type: Π b:α, Π _:Eq α a b, Sort v
    # building this: innermost Sort v, then wrap "_" binder with Eq α a b, then "b" with α.
    # inside the body of "_"-binder, we have α (3), a (2), b (1), _ (0). We need Sort v: no BVars.
    # Eq.{u} α a b at the moment of binding "_": surrounding scope has α a b (3 things).
    # α=BVar(2), a=BVar(1), b=BVar(0).
    motive_inner_eq = app_many(Const("Eq", (u,)), BVar(2), BVar(1), BVar(0))
    motive_inner = Pi("_", motive_inner_eq, Sort(v))
    # wrap b : α; surrounding scope just outside this layer (before motive binder):
    # α (BVar 1), a (BVar 0). So α here is BVar(1).
    motive_full = Pi("b", BVar(1), motive_inner)
    body = Pi("motive", motive_full, body)
    # wrap a : α; before wrapping a, scope has α (1 thing). α=BVar(0).
    body = Pi("a", BVar(0), body)
    # wrap α : Sort u
    body = Pi("α", α, body)

    # ι rule for Eq.rec on refl:
    #   Eq.rec α a motive m_refl a (Eq.refl α a)  →  m_refl
    # env_subst convention: params(α,a) ++ motives(motive) ++ minors(m_refl)
    #                       ++ fields() ++ rec_results()
    # Actually wait — for Eq, the constructor (refl) has num_fields=0.
    # But the recursor takes b (index!) and the major; in our framework
    # `num_indices=1`, so the kernel's `try_iota` requires num_indices == 0
    # to fire.  Eq's ι rule is special; we patch the kernel to allow indices
    # when they are determined by the constructor.
    #
    # For Eq.refl: the constructor's b-index equals `a`, so the recursor
    # application that reduces is  `Eq.rec α a motive m_refl a (Eq.refl α a)`.
    # In our kernel we currently bail when num_indices != 0.  We will extend
    # the kernel below to handle this Eq-style case by substituting the
    # constructor's "b" (which equals "a") and ignoring the index.

    # env_subst order for Eq.rec on refl:
    #   params: [α, a]
    #   motives_and_minors: [motive, m_refl]    (these are spine[2..3])
    #   fields: [] (refl has no fields)
    #   rec_results: []
    # Total entries = 4.  BVar(0) = m_refl, BVar(1) = motive, BVar(2) = a, BVar(3) = α.
    # RHS = m_refl = BVar(0)
    refl_rule = RecursorRule(
        ctor_name="Eq.refl",
        num_fields=0,
        num_rec_args=0,
        rhs_template=BVar(0),
        rec_arg_positions=(),
    )

    env.add(Recursor(
        name="Eq.rec",
        level_params=("u", "v"),
        type_=body,
        inductive="Eq",
        num_params=2,           # α, a
        num_motives=1,
        num_minors=1,
        num_indices=1,          # b
        motive_universe_param="v",
        rules=(refl_rule,),
    ))


# ---------- Nat helpers ----------

def _build_nat_ops(env: Env) -> None:
    """Define Nat.add and Nat.mul by recursion on the second argument."""
    Nat = Const("Nat", ())

    # Nat.add : Nat → Nat → Nat
    # Nat.add m n = Nat.rec.{1} (λ _:Nat. Nat) m (λ _:Nat. λ ih:Nat. Nat.succ ih) n
    rec_call = app_many(
        Const("Nat.rec", (LSucc(LZero()),)),         # motive lives in Type 0
        Lam("_", Nat, Nat),                          # motive
        BVar(1),                                     # m_zero = m
        Lam("k", Nat,
            Lam("ih", Nat,
                App(Const("Nat.succ", ()), BVar(0)))),
        BVar(0),                                     # major = n
    )
    add_value = Lam("m", Nat, Lam("n", Nat, rec_call))
    add_type = Pi("m", Nat, Pi("n", Nat, Nat))
    env.add(Definition("Nat.add", (), add_type, add_value))

    # Nat.mul : Nat → Nat → Nat
    # mul m n = Nat.rec (λ _. Nat) 0 (λ _ ih. add m ih) n
    mul_rec_call = app_many(
        Const("Nat.rec", (LSucc(LZero()),)),
        Lam("_", Nat, Nat),
        Const("Nat.zero", ()),
        Lam("k", Nat,
            Lam("ih", Nat,
                app_many(Const("Nat.add", ()), BVar(3), BVar(0)))),  # m = BVar(3)
        BVar(0),
    )
    mul_value = Lam("m", Nat, Lam("n", Nat, mul_rec_call))
    mul_type = Pi("m", Nat, Pi("n", Nat, Nat))
    env.add(Definition("Nat.mul", (), mul_type, mul_value))

    # Nat.pred : Nat → Nat
    # pred n = Nat.rec (λ _. Nat) 0 (λ k _. k) n
    pred_rec_call = app_many(
        Const("Nat.rec", (LSucc(LZero()),)),
        Lam("_", Nat, Nat),                      # motive
        Const("Nat.zero", ()),                   # m_zero = 0
        Lam("k", Nat, Lam("_ih", Nat, BVar(1))),  # step: return k
        BVar(0),                                  # major = n
    )
    pred_value = Lam("n", Nat, pred_rec_call)
    pred_type = Pi("n", Nat, Nat)
    env.add(Definition("Nat.pred", (), pred_type, pred_value))
