"""Profile a single test from tests/test_parser.py.

Usage:
    python scripts/profile_test.py test_parse_and_verify_decidable_eq_chain

Prints the top 30 functions by cumulative time, then the top 30 by
internal time.  Designed to find hot spots in the verifier/elaborator
that would benefit from algorithmic improvements (hash-consing,
memoization, etc.).

Saves a full .pstats file for follow-up exploration (snakeviz etc.).
"""
from __future__ import annotations
import sys, os, cProfile, pstats, argparse

# Make src/ + tests/ importable.
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)
sys.path.insert(0, os.path.join(ROOT, "tests"))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("test_name",
                    help="Name of a test function in tests/test_parser.py")
    ap.add_argument("--out", default="profile.pstats",
                    help="Where to dump the full pstats (default: profile.pstats)")
    args = ap.parse_args()

    import test_parser
    fn = getattr(test_parser, args.test_name, None)
    if fn is None:
        print(f"No such test: {args.test_name}", file=sys.stderr)
        sys.exit(1)

    pr = cProfile.Profile()
    pr.enable()
    fn()
    pr.disable()

    out_path = os.path.join(ROOT, args.out)
    pr.dump_stats(out_path)
    print(f"Wrote full stats to {out_path}")
    print()

    st = pstats.Stats(pr).sort_stats("cumulative")
    print("== top 30 by cumulative time ==")
    st.print_stats(30)

    st = pstats.Stats(pr).sort_stats("tottime")
    print("\n== top 30 by internal (self) time ==")
    st.print_stats(30)


if __name__ == "__main__":
    main()
