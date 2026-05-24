"""Parse a textual Lean-ish source file, build the env, emit, verify."""
from __future__ import annotations
import sys, os, io
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from src.env import Env
from src.prelude_decls import build_stdlib
from src.emitter import emit_env
from src.lean_parser import elaborate
from src.mm0_verify import verify_file, verify_text


HERE = os.path.dirname(os.path.abspath(__file__))
EXAMPLES = os.path.normpath(os.path.join(HERE, "..", "examples"))


def _run_example(*filenames: str):
    env = Env()
    build_stdlib(env)
    added_all: list = []
    for filename in filenames:
        with open(os.path.join(EXAMPLES, filename)) as f:
            src = f.read()
        added = elaborate(src, env)
        added_all.extend(added)
    out = io.StringIO()
    emit_env(env, out, only=added_all)
    venv = verify_file(os.path.join(HERE, "..", "prelude", "cic.mm0"))
    pre = io.StringIO()
    emit_env(env, pre, only=[n for n in env.order if n not in added_all])
    verify_text(pre.getvalue(), venv)
    verify_text(out.getvalue(), venv)


def test_parse_and_verify_demo():
    _run_example("demo.lean")


def test_parse_and_verify_vec():
    _run_example("vec.lean")


def test_parse_and_verify_algebra():
    _run_example("algebra.lean")


def test_parse_and_verify_order():
    _run_example("order.lean")


def test_parse_and_verify_match():
    _run_example("match.lean")


def test_parse_and_verify_match_list():
    _run_example("match_list.lean")


def test_parse_and_verify_implicits():
    _run_example("implicits.lean")


def test_parse_and_verify_no_levels():
    _run_example("no_levels.lean")


def test_parse_and_verify_typeclass():
    _run_example("typeclass.lean")


def test_parse_and_verify_arith():
    _run_example("arith.lean")


def test_parse_and_verify_hop():
    _run_example("hop.lean")


def test_parse_and_verify_algebra2():
    _run_example("algebra2.lean")


def test_parse_and_verify_at_syntax():
    _run_example("at_syntax.lean")


def test_parse_and_verify_parametric_inst():
    _run_example("parametric_inst.lean")


def test_parse_and_verify_recursion():
    _run_example("recursion.lean")


def test_parse_and_verify_list_rec():
    _run_example("list_rec.lean")


def test_parse_and_verify_inherit():
    _run_example("inherit.lean")


def test_parse_and_verify_comparison():
    _run_example("comparison.lean")


def test_parse_and_verify_list_ops():
    _run_example("list_ops.lean")


def test_parse_and_verify_math():
    _run_example("math.lean")


def test_parse_and_verify_tactics():
    _run_example("tactics.lean")


def test_parse_and_verify_apply():
    _run_example("apply.lean")


def test_parse_and_verify_decidable():
    _run_example("decidable.lean")


def test_parse_and_verify_intro_seq():
    _run_example("intro_seq.lean")


def test_parse_and_verify_dep_match():
    _run_example("dep_match.lean")


def test_parse_and_verify_mid_seq():
    _run_example("mid_seq.lean")


def test_parse_and_verify_idx_match():
    _run_example("idx_match.lean")


def test_parse_and_verify_nat_lemmas():
    # nat_lemmas builds on math's zero_add / succ_add
    _run_example("math.lean", "nat_lemmas.lean")


def test_parse_and_verify_rewrite():
    _run_example("rewrite.lean")


def test_parse_and_verify_decidable_compose():
    _run_example("decidable_compose.lean")


if __name__ == "__main__":
    tests = [v for k, v in list(globals().items()) if k.startswith("test_")]
    passed = failed = 0
    for t in tests:
        try:
            t()
            print(f"  ok  {t.__name__}")
            passed += 1
        except Exception as e:
            import traceback
            traceback.print_exc()
            print(f"FAIL  {t.__name__}: {e}")
            failed += 1
    print(f"\n{passed} passed, {failed} failed")
    sys.exit(0 if failed == 0 else 1)
