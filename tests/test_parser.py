"""Parse a textual Lean-ish source file, build the env, emit, verify."""
from __future__ import annotations
import sys, os, io, copy
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from src.env import Env
from src.prelude_decls import build_stdlib
from src.emitter import emit_env
from src.lean_parser import elaborate
from src.mm0_verify import verify_file, verify_text


HERE = os.path.dirname(os.path.abspath(__file__))
EXAMPLES = os.path.normpath(os.path.join(HERE, "..", "examples"))


# Cache the parsed-and-verified prelude across tests.  Every test
# used to call `verify_file(prelude/cic.mm0)` from scratch — a few
# hundred ms each, multiplied across ~60 tests was significant suite
# time.  We parse once at module load, then deepcopy for each test so
# the per-test `verify_text` calls that mutate the venv don't leak
# between tests.
_PRELUDE_VENV = verify_file(os.path.join(HERE, "..", "prelude", "cic.mm0"))


def _fresh_prelude_venv():
    return copy.deepcopy(_PRELUDE_VENV)


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
    venv = _fresh_prelude_venv()
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


def test_parse_and_verify_nat_inj():
    _run_example("nat_inj.lean")


def test_parse_and_verify_nat_dec_eq():
    _run_example("nat_inj.lean", "nat_dec_eq.lean")


def test_parse_and_verify_bool_dec_eq():
    _run_example("bool_dec_eq.lean")


def test_parse_and_verify_bool_ops():
    _run_example("bool_ops.lean")


def test_parse_and_verify_nat_le():
    _run_example("nat_le.lean")


def test_parse_and_verify_cases():
    _run_example("cases.lean")


def test_parse_and_verify_nat_lt():
    _run_example("nat_le.lean", "nat_lt.lean")


def test_parse_and_verify_nat_le_more():
    _run_example("nat_le.lean", "nat_lt.lean", "nat_le_more.lean")


def test_parse_and_verify_indexed_cases():
    _run_example("indexed_cases.lean")


def test_parse_and_verify_idx_match_rec():
    # match on an indexed inductive with a recursive ctor (Nat.le.step).
    _run_example("idx_match_rec.lean")


def test_parse_and_verify_induction_auto_revert():
    _run_example("induction_auto_revert.lean")


def test_parse_and_verify_nat_le_chain():
    # pred_le_pred + lt_irrefl, exercising index unification and
    # auto-revert for `induction`.  Depends on nat_le, nat_lt for
    # base lemmas, nat_inj for succ_inj, index_unif for
    # not_succ_le_zero.
    _run_example("nat_inj.lean", "nat_le.lean", "nat_lt.lean",
                 "nat_le_more.lean", "index_unif.lean",
                 "nat_le_chain.lean")


def test_parse_and_verify_nat_dec_le():
    # Decidable Le / Lt for Nat.  Uses helpers from nat_le_more,
    # index_unif, and pred_le_pred from nat_le_chain.
    _run_example("nat_inj.lean", "nat_le.lean", "nat_lt.lean",
                 "nat_le_more.lean", "index_unif.lean",
                 "nat_le_chain.lean", "nat_dec_le.lean")


def test_parse_and_verify_have():
    # `have h : T := e` tactic.  add_comm + zero_add are from math.lean.
    _run_example("math.lean", "have.lean")


def test_parse_and_verify_list_mem():
    # List membership + Decidable.  Uses Nat.decEq from nat_dec_eq,
    # instDecidableOr from decidable_compose.
    _run_example("nat_inj.lean", "nat_dec_eq.lean",
                 "decidable_compose.lean", "list_mem.lean")


def test_parse_and_verify_decidable_eq():
    # DecidableEq class + instance for Nat + class-driven List.decMem.
    _run_example("nat_inj.lean", "nat_dec_eq.lean",
                 "decidable_compose.lean", "list_mem.lean",
                 "decidable_eq.lean")


def test_parse_and_verify_infix_multi():
    _run_example("infix_multi.lean")


def test_parse_and_verify_notation_brackets():
    _run_example("notation_brackets.lean")


def test_parse_and_verify_rw_multi():
    _run_example("rw_multi.lean")


def test_parse_and_verify_decidable_eq_chain():
    # DecidableEq for Bool and List (parametric over element DecidableEq).
    # Uses Bool.decEq from bool_dec_eq, polymorphic List.decEq from
    # list_dec_eq_poly, and the DecidableEq class from decidable_eq.
    _run_example("nat_inj.lean", "nat_dec_eq.lean", "bool_dec_eq.lean",
                 "list_dec_eq_poly.lean", "decidable_compose.lean",
                 "list_mem.lean", "decidable_eq.lean",
                 "decidable_eq_chain.lean")


def test_parse_and_verify_option_ops():
    # Option utilities + Option.decEq.  Uses Nat.decEq for the
    # sanity-check examples.
    _run_example("nat_inj.lean", "nat_dec_eq.lean", "option_ops.lean")


def test_parse_and_verify_revert():
    # revert example uses zero_add, succ_add, lift_succ from
    # math.lean / nat_lemmas.lean.
    _run_example("math.lean", "nat_lemmas.lean", "revert.lean")


def test_parse_and_verify_list_dec_eq():
    # Uses Nat.decEq from nat_dec_eq.lean (which itself needs nat_inj.lean).
    _run_example("nat_inj.lean", "nat_dec_eq.lean", "list_dec_eq.lean")


def test_parse_and_verify_list_dec_eq_poly():
    _run_example("nat_inj.lean", "nat_dec_eq.lean", "list_dec_eq_poly.lean")


def test_parse_and_verify_list_theorems():
    _run_example("math.lean", "nat_lemmas.lean", "list_ops.lean",
                 "list_theorems.lean")


def test_parse_and_verify_simp():
    _run_example("math.lean", "nat_lemmas.lean", "simp.lean")


def test_parse_and_verify_index_unif():
    # Index unification needs succ_ne_zero from nat_inj.lean.
    _run_example("nat_inj.lean", "index_unif.lean")


def test_parse_and_verify_nat_mul():
    _run_example("math.lean", "nat_lemmas.lean", "nat_mul.lean")


def test_parse_and_verify_induction():
    # induction uses lift_succ + succ_add from math.lean / nat_lemmas.lean,
    # Bool.not from bool_ops.lean, length + append from list_ops.lean.
    _run_example("math.lean", "nat_lemmas.lean", "bool_ops.lean",
                 "list_ops.lean", "induction.lean")




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
