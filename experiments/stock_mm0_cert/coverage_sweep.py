"""Coverage sweep DRIVER: run coverage_worker.py over every examples/*.lean
(one subprocess per file) and print a fresh coverage table + headline.

Deliberately prints rather than bakes numbers into a doc: the figures shift as
the bridge grows, so the source of truth is *running this*, not a stale table.
Usage:  python3 coverage_sweep.py
"""
import os, re, sys, subprocess, collections

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
EXAMPLES = sorted(f for f in os.listdir(f"{ROOT}/examples") if f.endswith(".lean"))

def run_one(fname):
    path = f"{ROOT}/examples/{fname}"
    try:
        out = subprocess.run([sys.executable, f"{HERE}/coverage_worker.py", path],
                             capture_output=True, text=True, timeout=300)
        for line in out.stdout.splitlines():
            if line.startswith("RESULT "):
                return line
    except subprocess.TimeoutExpired:
        pass
    return (f"RESULT {fname} elaborated=ERR obligs=0 certified=0 skipped=0 "
            f"rs_rc=-5 cc_rc=-5 faithful=NA nodes=- reasons=timeout")

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
    obl  = sum(gi(r, "obligs") for r in ok)
    cert = sum(gi(r, "certified") for r in ok)
    skip = sum(gi(r, "skipped") for r in ok)
    full = sum(1 for r in ok if gi(r, "obligs") > 0 and gi(r, "skipped") == 0)
    part = sum(1 for r in ok if gi(r, "certified") > 0 and gi(r, "skipped") > 0)
    withc = sum(1 for r in ok if gi(r, "certified") > 0)
    # invariant: every file with >=1 certified obligation passes both checkers
    bad = [r.split()[1] for r in ok if gi(r, "certified") > 0
           and not (gi(r, "rs_rc") == 0 and gi(r, "cc_rc") == 0)]

    print("\n## Per-file (elaborated)\n")
    print("| file | obligations | certified | mm0-rs | mm0-c |")
    print("|---|---|---|---|---|")
    def mark(rc): return "—" if rc in (-2, -3, -4, -5) else ("OK" if rc == 0 else "FAIL")
    for r in sorted(ok, key=lambda r: (-gi(r, "certified"), r.split()[1])):
        name = r.split()[1]
        print("| `%s` | %d | %d | %s | %s |" % (name, gi(r, "obligs"), gi(r, "certified"),
                                                mark(gi(r, "rs_rc")), mark(gi(r, "cc_rc"))))

    # aggregate the per-file skip tags so the sweep names its own next targets
    reasons = collections.Counter()
    for r in ok:
        m = re.search(r" reasons=(\S+)", r)
        if not m or m.group(1) == "-":
            continue
        for tag in m.group(1).split(","):
            if tag and tag != "-":
                reasons[tag] += 1
    if reasons:
        print("\n## Top skip reasons (files blocked, by construct)\n")
        for tag, c in reasons.most_common():
            print("- `%s` — %d file(s)" % (tag, c))

    print("\n## Headline (regenerated this run)\n")
    print(f"- {len(rows)} example files swept; {len(ok)} elaborate here, {len(err)} do not")
    print(f"  (the latter reference decls this standalone build_stdlib lacks -- a harness gap).")
    print(f"- {obl} de-refl obligations (Eq over any type) across the elaborated files;")
    print(f"  {cert} certified through stock mm0-c, {skip} skipped (out of bridged fragment).")
    print(f"- {withc} files with >=1 certified obligation ({full} fully, {part} partially).")
    print(f"- invariant 'every certified file passes BOTH mm0-rs and mm0-c': "
          f"{'OK' if not bad else 'VIOLATED ' + ','.join(bad)}")
    if bad:
        sys.exit(1)

if __name__ == "__main__":
    main()
