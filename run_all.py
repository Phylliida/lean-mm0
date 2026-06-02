"""Run every test in the project, reporting overall pass/fail."""
from __future__ import annotations
import sys, os, subprocess

HERE = os.path.dirname(os.path.abspath(__file__))

# Legacy suite: parser / elaborator / kernel, plus the legacy emitter -> mm0_verify.py
# path (test_emit_basic / suite / test_parser).  mm0_verify.py is being retired in favour
# of stock MM0; these stay during the transition (they still use the full stdlib, so they
# cover the ~19 examples that don't yet elaborate under the standalone stock harness).
TESTS = [
    "tests/test_kernel_smoke.py",
    "tests/test_emit_basic.py",
    "tests/suite.py",
    "tests/test_parser.py",
]

# Stock-MM0 verification GATE (the new direction): certify examples/ against stock MM0
# (db.mm1 + the 815-line checker) via verify.py -- no Python evaluator in the trusted
# base.  Runs ALONGSIDE the legacy suite during the swap.  Fails the run only on a
# REJECTED file; the harness-gap files that don't elaborate standalone are reported as
# skipped, not failures.
STAGES = [(t, [t]) for t in TESTS] + [
    ("stock-MM0 verify (verify.py --all)", ["verify.py", "--all"]),
]


def main() -> int:
    total_fail = 0
    for label, argv in STAGES:
        print(f"=== {label} " + "=" * max(0, 60 - len(label)))
        res = subprocess.run([sys.executable, os.path.join(HERE, argv[0])] + argv[1:],
                             cwd=HERE)
        if res.returncode != 0:
            total_fail += 1
    print()
    if total_fail == 0:
        print(f"All {len(STAGES)} stages passed.")
        return 0
    print(f"{total_fail}/{len(STAGES)} stages failed.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
