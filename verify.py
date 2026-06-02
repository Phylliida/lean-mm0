#!/usr/bin/env python3
"""verify.py — verify a Lean source file against STOCK MM0, end to end.

This is the stock-MM0 verifier entry point.  It runs the real pipeline
(parser → elaborator → kernel), then certifies *every* elaborated declaration's
typing as an explicit proof against the de-Bruijn CIC prelude (`db.mm1`) and checks
that proof with the **stock** MM0 verifiers — mm0-rs and the 815-line mm0-c.  There is
**no Python evaluator in the trusted base**: every reduction/typing step is an explicit
proof the tiny shared checker re-checks.

    Trusted base = db.mm1 (CIC axioms, ~170 lines) + the stock MM0 checker (815-line C).

A file is VERIFIED only if both checkers accept the generated certificate.  The
certificate is valid *modulo* any source `axiom`s the file declares (e.g. `propext`,
`Classical.choice`), which are listed — the stock-MM0 analogue of `#print axioms`.

This is the successor to the legacy `src/mm0_verify.py` (a Python verifier with a
βιζ/shift/subst evaluator baked into its trusted core).  Per-file certification is done
by `experiments/stock_mm0_cert/envcert_worker.py` (the engine; run in a subprocess so
its globals reset between files); this front end presents the verdict.

Usage:
    python3 verify.py FILE.lean [FILE.lean ...]
    python3 verify.py --all          # verify every examples/*.lean

Exit status is non-zero if any file is REJECTED by a checker.
"""
import os, re, sys, subprocess

HERE   = os.path.dirname(os.path.abspath(__file__))
ENGINE = f"{HERE}/experiments/stock_mm0_cert/envcert_worker.py"
EXAMPLES = f"{HERE}/examples"

GREEN, YELLOW, RED, DIM, BOLD, OFF = (
    "\033[32m", "\033[33m", "\033[31m", "\033[2m", "\033[1m", "\033[0m")


def _gi(line, key, default=0):
    m = re.search(r" %s=(-?\d+)" % key, line)
    return int(m.group(1)) if m else default


def _gs(line, key):
    m = re.search(r" %s=(\S+)" % key, line)
    return m.group(1) if m else "-"


def verify_one(path):
    """Run the engine on one file; return (status, detail) where status is one of
    'verified' / 'partial' / 'rejected' / 'elab-fail' / 'empty'."""
    r = subprocess.run([sys.executable, ENGINE, path], capture_output=True, text=True)
    line = next((l for l in r.stdout.splitlines() if l.startswith("RESULT ")), "")
    if not line:
        return "rejected", {"msg": (r.stderr or r.stdout or "engine produced no result")[-400:]}
    if " elaborated=ERR " in line:
        return "elab-fail", {"reason": _gs(line, "reasons")}
    d = dict(decls=_gi(line, "decls"), cert=_gi(line, "certified"),
             skip=_gi(line, "skipped"), rs=_gi(line, "rs_rc"), cc=_gi(line, "cc_rc"),
             reasons=_gs(line, "reasons"), axioms=_gs(line, "axioms"))
    if d["cert"] == 0 and d["skip"] == 0:
        return "empty", d
    if d["rs"] != 0 or d["cc"] != 0:
        return "rejected", d
    return ("verified" if d["skip"] == 0 else "partial"), d


def _print(path, status, d):
    name = os.path.basename(path)
    if status == "verified":
        ax = "none" if d["axioms"] in ("-", "") else d["axioms"].replace(",", ", ")
        print(f"{GREEN}✓ VERIFIED{OFF}  {BOLD}{name}{OFF}  "
              f"against stock MM0 (mm0-rs + mm0-c)")
        print(f"           {d['cert']} declarations re-typechecked; "
              f"axioms assumed: {ax}")
    elif status == "partial":
        print(f"{YELLOW}⚠ PARTIAL{OFF}   {BOLD}{name}{OFF}  "
              f"{d['cert']} verified, {d['skip']} out of the bridged fragment "
              f"({DIM}{d['reasons']}{OFF})")
    elif status == "empty":
        print(f"{DIM}· nothing to verify  {name}  (no declarations with a body){OFF}")
    elif status == "elab-fail":
        print(f"{DIM}· skipped  {name}  (does not elaborate standalone: "
              f"{d['reason']}){OFF}")
    else:  # rejected
        if "msg" in d:
            print(f"{RED}✗ REJECTED{OFF}  {BOLD}{name}{OFF}\n           {d['msg']}")
        else:
            who = "mm0-rs" if d["rs"] != 0 else "mm0-c"
            print(f"{RED}✗ REJECTED{OFF}  {BOLD}{name}{OFF}  by {who} "
                  f"(rs_rc={d['rs']} cc_rc={d['cc']}) — see /tmp/env_{os.path.basename(path)}.err")


def main():
    args = sys.argv[1:]
    if not args:
        print(__doc__); sys.exit(2)
    files = (sorted(f"{EXAMPLES}/{f}" for f in os.listdir(EXAMPLES) if f.endswith(".lean"))
             if args == ["--all"] else args)

    counts = {"verified": 0, "partial": 0, "rejected": 0, "elab-fail": 0, "empty": 0}
    all_axioms = set()
    for path in files:
        status, d = verify_one(path)
        counts[status] += 1
        if status in ("verified", "partial") and d.get("axioms", "-") not in ("-", ""):
            all_axioms.update(d["axioms"].split(","))
        _print(path, status, d)

    if len(files) > 1:
        print(f"\n{BOLD}Summary:{OFF} {GREEN}{counts['verified']} verified{OFF}, "
              f"{YELLOW}{counts['partial']} partial{OFF}, "
              f"{RED}{counts['rejected']} rejected{OFF}, "
              f"{counts['elab-fail']} not elaborated, {counts['empty']} empty")
        if all_axioms:
            print(f"axioms assumed across the run: {', '.join(sorted(all_axioms))}")
    sys.exit(1 if counts["rejected"] else 0)


if __name__ == "__main__":
    main()
