"""Whole-ENVIRONMENT certification sweep DRIVER: run envcert_worker.py over every
examples/*.lean and print how much of the FULL elaborated environment the 815-line
stock base re-typechecks -- every declaration, not just its `Eq` goals.

The stronger sibling of coverage_sweep.py: that one measures de-refl / proof
*obligations* (Eq goals); this one measures *declarations* -- every theorem and def
the kernel elaborated, certified by typing `ht cnil value type` through stock MM0.

Deliberately prints rather than bakes numbers (they shift as the bridge grows).
Usage:  python3 envcert_sweep.py
"""
import os, re, sys, subprocess, collections

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
EXAMPLES = sorted(f for f in os.listdir(f"{ROOT}/examples") if f.endswith(".lean"))


def run_one(fname):
    path = f"{ROOT}/examples/{fname}"
    try:
        out = subprocess.run([sys.executable, f"{HERE}/envcert_worker.py", path],
                             capture_output=True, text=True, timeout=600)
        for line in out.stdout.splitlines():
            if line.startswith("RESULT "):
                return line
    except subprocess.TimeoutExpired:
        pass
    return (f"RESULT {fname} elaborated=ERR decls=0 certified=0 skipped=0 "
            f"rs_rc=-5 cc_rc=-5 nodes=- reasons=timeout")


def gi(line, key):
    m = re.search(r" %s=(-?\d+)" % key, line)
    return int(m.group(1)) if m else 0


def main():
    rows = []
    for f in EXAMPLES:
        line = run_one(f)
        rows.append(line)
        print(line, file=sys.stderr)              # progress to stderr

    ok  = [r for r in rows if " elaborated=ERR " not in r]
    err = [r for r in rows if " elaborated=ERR " in r]
    decls = sum(gi(r, "decls") for r in ok)
    cert  = sum(gi(r, "certified") for r in ok)
    skip  = sum(gi(r, "skipped") for r in ok)
    full  = sum(1 for r in ok if gi(r, "decls") > 0 and gi(r, "skipped") == 0)
    part  = sum(1 for r in ok if gi(r, "certified") > 0 and gi(r, "skipped") > 0)
    withc = sum(1 for r in ok if gi(r, "certified") > 0)
    # invariant: every file with >=1 certified decl passes both checkers
    bad = [r.split()[1] for r in ok if gi(r, "certified") > 0
           and not (gi(r, "rs_rc") == 0 and gi(r, "cc_rc") == 0)]

    print("\n## Per-file (elaborated)\n")
    print("| file | decls | certified | mm0-rs | mm0-c |")
    print("|---|---|---|---|---|")
    def mark(rc): return "—" if rc in (-2, -3, -4, -5) else ("OK" if rc == 0 else "FAIL")
    for r in sorted(ok, key=lambda r: (-gi(r, "certified"), r.split()[1])):
        name = r.split()[1]
        print("| `%s` | %d | %d | %s | %s |" % (name, gi(r, "decls"), gi(r, "certified"),
                                                mark(gi(r, "rs_rc")), mark(gi(r, "cc_rc"))))

    reasons = collections.Counter()
    for r in ok:
        m = re.search(r" reasons=(\S+)", r)
        if not m or m.group(1) == "-":
            continue
        for tag in m.group(1).split(","):
            if tag and tag != "-":
                reasons[tag] += 1
    if reasons:
        print("\n## Top skip reasons (declarations the stock base couldn't re-type)\n")
        for tag, c in reasons.most_common():
            print("- `%s` — %d file(s)" % (tag, c))

    print("\n## Headline (regenerated this run)\n")
    print(f"- {len(rows)} example files swept; {len(ok)} elaborate here, {len(err)} do not")
    print(f"  (the latter reference decls this standalone build_stdlib lacks -- a harness gap).")
    print(f"- {decls} declarations (every elaborated theorem/def with a body) across those files;")
    print(f"  {cert} RE-TYPECHECKED end-to-end by the 815-line stock mm0-c (typed `ht cnil"
          f" body type`), {skip} skipped (out of bridged fragment).")
    print(f"- {withc} files with >=1 certified decl ({full} fully, {part} partially).")
    print(f"- invariant 'every certified file passes BOTH mm0-rs and mm0-c': "
          f"{'OK' if not bad else 'VIOLATED ' + ','.join(bad)}")
    if bad:
        sys.exit(1)


if __name__ == "__main__":
    main()
