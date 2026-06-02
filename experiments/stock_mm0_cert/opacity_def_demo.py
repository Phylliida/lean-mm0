"""Per-feature demo: OPACITY FOR DEFS -- type each def ONCE, reference it everywhere.

A `def` is DELTA-TRANSPARENT: the kernel (and stock mm0) unfold its body to COMPUTE.
That is right for reduction, but it made the certifier re-derive the def's TYPING at
every use site -- and a `Decidable`-equality instance is a def whose typing is large,
so a proof that branches on it many times produced a multi-megabyte certificate that
overflowed the 815-line mm0-c's store.  This is the proof-SIZE wall HANDOFF recorded.

The fix mirrors the opaque-lemma `htop` trick, but keeps the def transparent for
computation: each def gets ONE `htdef_<name> (g: ctx): ht g <name> <type>` typing
theorem (proved once -- g-polymorphic, since a closed body types context-independently),
and every prove_ht of the def REFERENCES `(htdef_<name>)` instead of re-typing the body.
The def stays in DEFS, so whnf still delta-unfolds it to reduce.  No trusted axiom, no
trusted-base change (db.mm1 byte-identical) -- the htdef theorem is generated + checked
like everything else.

This is the enabler that takes `examples/list_dec_eq.lean` (decidable equality over
lists of Nat -- DecidableEq instances branched on repeatedly) from a proof-size wall to
a clean certificate accepted by BOTH stock checkers.  This demo runs that real example
through the whole-environment worker and derives the sharing it bought.
"""
import os, re, subprocess, sys, collections

HERE = os.path.dirname(os.path.abspath(__file__))
E    = os.path.normpath(f"{HERE}/../../examples")
CHAIN = [f"{E}/nat_inj.lean", f"{E}/nat_dec_eq.lean", f"{E}/list_dec_eq.lean"]
MM1   = "/tmp/env_list_dec_eq.lean.mm1"


def nodes_of(proof):
    return len(re.findall(r"[A-Za-z_]\w*", proof))


def main():
    out = subprocess.run([sys.executable, f"{HERE}/envcert_worker.py", *CHAIN],
                         capture_output=True, text=True)
    line = next((l for l in out.stdout.splitlines() if l.startswith("RESULT ")), "")
    m = re.search(r"certified=(\d+) skipped=(\d+) rs_rc=(-?\d+) cc_rc=(-?\d+)", line)
    cert, skip, rs, cc = (m.groups() if m else ("?", "?", "?", "?"))
    ok = (rs == "0" and cc == "0")

    print(__doc__.strip())
    print(f"\n  chain: {' -> '.join(os.path.basename(f) for f in CHAIN)}")
    print(f"  result: certified={cert} skipped={skip}  mm0-rs rc={rs}  mm0-c rc={cc}"
          f"   {'BOTH CHECKERS OK' if ok else 'CHECKER FAIL'}")

    if not os.path.exists(MM1):
        print("\n(no cert emitted)"); sys.exit(1)
    mm1 = open(MM1).read()

    # each htdef theorem = one def typed ONCE; count how often each is referenced.
    htdef_proof = {name: proof for name, proof in
                   re.findall(r"theorem (htdef_\w+)[^=]*=\s*'(.*?);", mm1, re.S)}
    refs = collections.Counter(re.findall(r"\((htdef_\w+)\)", mm1))
    n_defs   = len(htdef_proof)
    n_refs   = sum(refs.values())
    once_cost   = sum(nodes_of(p) for p in htdef_proof.values())          # typed once
    inline_cost = sum(refs[name] * nodes_of(htdef_proof.get(name, ""))    # if re-typed
                      for name in refs)

    print(f"\n  defs typed ONCE (htdef theorems):      {n_defs}")
    print(f"  total references to those typings:     {n_refs}")
    print(f"  typing-proof nodes, typed once:        {once_cost:,}")
    print(f"  typing-proof nodes if INLINED per use: {inline_cost:,}"
          f"   ({inline_cost/max(once_cost,1):.0f}x)")
    print("\n  most-shared defs (typed once, referenced N times):")
    for name, n in refs.most_common(6):
        print(f"    {name[6:]:<24} used {n:>3}x   (typing {nodes_of(htdef_proof.get(name,'')):>5} nodes, shared)")
    print("\n  -> opacity-for-defs collapses the repeated typing of the DecidableEq")
    print("     machinery (e.g. Nat.decEq) from inline-per-use to one shared theorem,")
    print("     bringing the certificate back under the 815-line mm0-c's store.")
    print("\nopacity-for-defs certified by BOTH checkers:", "OK" if ok else "FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
