"""Smoke tests for the kernel: build the stdlib, type-check small terms,
reduce a few computations."""
from __future__ import annotations
import sys, os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from src.levels import LZero, LSucc, LParam
from src.expr import Sort, BVar, Const, App, Lam, Pi, app_many
from src.env import Env, Definition
from src.kernel import Kernel, LocalCtx, TypeError_
from src.prelude_decls import build_stdlib, TYPE0


def setup() -> tuple[Env, Kernel]:
    env = Env()
    build_stdlib(env)
    return env, Kernel(env)


def nat_lit(n: int):
    e = Const("Nat.zero", ())
    for _ in range(n):
        e = App(Const("Nat.succ", ()), e)
    return e


def test_nat_zero_typing():
    env, k = setup()
    ty, _ = k.infer(Const("Nat.zero", ()), LocalCtx())
    assert ty == Const("Nat", ()), ty


def test_succ_typing():
    env, k = setup()
    ty, _ = k.infer(nat_lit(3), LocalCtx())
    assert ty == Const("Nat", ()), ty


def test_add_two_two():
    env, k = setup()
    ctx = LocalCtx()
    add22 = app_many(Const("Nat.add", ()), nat_lit(2), nat_lit(2))
    ty, _ = k.infer(add22, ctx)
    assert ty == Const("Nat", ()), ty
    # check it reduces to 4
    red = k.whnf(add22, ctx)
    # whnf only reduces the head; for a Nat literal we expect successive
    # ι-reductions to expose Nat.succ ^ 4 Nat.zero
    def force(e, k, ctx):
        if isinstance(e, App):
            f = force(e.fn, k, ctx)
            a = force(e.arg, k, ctx)
            x = k.whnf(App(f, a), ctx)
            return x if not isinstance(x, App) else App(f, a)
        return k.whnf(e, ctx)
    # easier: convert to integer
    def to_int(e):
        e = k.whnf(e, ctx)
        if isinstance(e, Const) and e.name == "Nat.zero":
            return 0
        if isinstance(e, App) and isinstance(e.fn, Const) and e.fn.name == "Nat.succ":
            return 1 + to_int(e.arg)
        raise AssertionError(f"not a Nat literal: {e}")
    assert to_int(add22) == 4


def test_list_cons():
    env, k = setup()
    ctx = LocalCtx()
    # cons.{1} Nat 0 nil
    nil = app_many(Const("List.nil", (LSucc(LZero()),)), Const("Nat", ()))
    one_elem = app_many(
        Const("List.cons", (LSucc(LZero()),)),
        Const("Nat", ()),
        Const("Nat.zero", ()),
        nil,
    )
    ty, _ = k.infer(one_elem, ctx)
    expected = App(Const("List", (LSucc(LZero()),)), Const("Nat", ()))
    assert ty == expected, (ty, expected)


def test_id_function():
    env, k = setup()
    # id : Π α : Type 0, α → α
    id_ty = Pi("α", TYPE0, Pi("x", BVar(0), BVar(1)))
    id_val = Lam("α", TYPE0, Lam("x", BVar(0), BVar(0)))
    # type-check the value against the type
    k.check(id_val, id_ty, LocalCtx())


def test_id_application():
    env, k = setup()
    id_val = Lam("α", TYPE0, Lam("x", BVar(0), BVar(0)))
    applied = app_many(id_val, Const("Nat", ()), nat_lit(3))
    ty, _ = k.infer(applied, LocalCtx())
    assert ty == Const("Nat", ()), ty


def test_eq_refl():
    env, k = setup()
    # Eq.refl.{1} Nat 0 : Eq.{1} Nat 0 0
    refl = app_many(Const("Eq.refl", (LSucc(LZero()),)),
                    Const("Nat", ()), nat_lit(0))
    ty, _ = k.infer(refl, LocalCtx())
    expected = app_many(Const("Eq", (LSucc(LZero()),)),
                        Const("Nat", ()), nat_lit(0), nat_lit(0))
    assert ty == expected, (ty, expected)


if __name__ == "__main__":
    tests = [v for k, v in list(globals().items()) if k.startswith("test_")]
    passed = failed = 0
    for t in tests:
        try:
            t()
            passed += 1
            print(f"  ok  {t.__name__}")
        except Exception as e:
            failed += 1
            print(f"FAIL  {t.__name__}: {type(e).__name__}: {e}")
    print(f"\n{passed} passed, {failed} failed")
    sys.exit(0 if failed == 0 else 1)
