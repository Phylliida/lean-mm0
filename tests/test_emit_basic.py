"""End-to-end: build stdlib, emit, verify with the MM0 verifier."""
from __future__ import annotations
import sys, os, io, tempfile
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from src.env import Env
from src.prelude_decls import build_stdlib
from src.emitter import emit_env
from src.mm0_verify import verify_file, verify_text, VerifyError


def emit_to_text(names=None):
    env = Env()
    build_stdlib(env)
    out = io.StringIO()
    emit_env(env, out, only=names)
    return out.getvalue()


def test_emit_bool():
    text = emit_to_text(["Bool", "Bool.false", "Bool.true", "Bool.rec"])
    env = verify_file("prelude/cic.mm0")
    verify_text(text, env)


def test_emit_nat_no_recurse():
    text = emit_to_text(["Nat", "Nat.zero", "Nat.succ", "Nat.rec"])
    env = verify_file("prelude/cic.mm0")
    verify_text(text, env)


def test_emit_full_stdlib():
    text = emit_to_text()           # everything
    env = verify_file("prelude/cic.mm0")
    verify_text(text, env)


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
