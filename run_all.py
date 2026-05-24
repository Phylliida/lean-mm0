"""Run every test in the project, reporting overall pass/fail."""
from __future__ import annotations
import sys, os, subprocess

HERE = os.path.dirname(os.path.abspath(__file__))
TESTS = [
    "tests/test_kernel_smoke.py",
    "tests/test_emit_basic.py",
    "tests/suite.py",
    "tests/test_parser.py",
]


def main() -> int:
    total_fail = 0
    for t in TESTS:
        path = os.path.join(HERE, t)
        print(f"=== {t} " + "=" * (60 - len(t)))
        res = subprocess.run([sys.executable, path], cwd=HERE)
        if res.returncode != 0:
            total_fail += 1
    print()
    if total_fail == 0:
        print(f"All {len(TESTS)} test files passed.")
        return 0
    print(f"{total_fail}/{len(TESTS)} test files failed.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
