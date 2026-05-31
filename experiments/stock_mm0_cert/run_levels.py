"""Universe-level equations certified against stock MM0.

The kernel decides `Sort u ≡ Sort v` by normalising the universe levels (a
semilattice with lz / lS / lmax / limax) and comparing.  db.mm1 had the level
*operations* but no level-*equality* judgment, so two universe-equal sorts could
only be proven equal when syntactically identical.

This adds the semilattice laws (`leveq`, a fixed spec block in db.mm1 -- like
ht_pi) and a db_cert normalizer that emits explicit `leveq` proofs, so e.g.
`max 0 1 = 1`, `max 2 3 = 3`, `imax 2 0 = 0` (impredicativity), `imax 2 3 = 3`
all certify, and `deq cnil (esort L1) (esort L2)` follows via `deq_sort`.

Closed levels (towers of lS over lz, combined with lmax/limax) normalise to a
numeral, which is the bridge's current scope; open/param levels (idempotence,
commutativity) are shown via a single parametric theorem and left as follow-up.
"""
import os, sys, subprocess

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import db_cert
from db_cert import ESort, prove_conv, proof_nodes

MM0   = "/home/bepis/prog/scientific-computing/mm0"
MM0RS = f"{MM0}/mm0-rs/target/release/mm0-rs"
MM0C  = f"{MM0}/mm0-c/mm0-c-np"

def lnum(n):
    s = "lz"
    for _ in range(n):
        s = f"(lS {s})"
    return s
lmax  = lambda a, b: f"(lmax {a} {b})"
limax = lambda a, b: f"(limax {a} {b})"


def main():
    log = []
    LG = lambda *a: log.append(" ".join(str(x) for x in a))

    # closed level equations: prove deq cnil (esort L1) (esort L2)
    cases = [
        ("max_0_1",  lmax(lnum(0), lnum(1)),  lnum(1)),
        ("max_1_1",  lmax(lnum(1), lnum(1)),  lnum(1)),
        ("max_2_3",  lmax(lnum(2), lnum(3)),  lnum(3)),
        ("max_3_2",  lmax(lnum(3), lnum(2)),  lnum(3)),
        ("imax_2_0", limax(lnum(2), lnum(0)), lnum(0)),   # impredicative: codomain 0
        ("imax_2_3", limax(lnum(2), lnum(3)), lnum(3)),
        ("nested",   lmax(lnum(1), lmax(lnum(0), lnum(2))), lnum(2)),
    ]
    results = []
    thms = []
    for label, l1, l2 in cases:
        conv = prove_conv(ESort(l1), ESort(l2)) or "(deq_refl)"
        n = proof_nodes(conv)
        LG(label, l1, "=", l2, "->", n, "nodes")
        results.append((label, n))
        thms.append(f"theorem lvl_{label}: $ deq cnil (esort {l1}) (esort {l2}) $ =\n'{conv};\n")

    # one OPEN (parametric) law to exercise idempotence: leveq (lmax u u) u
    thms.append("theorem lvl_maxid (u: lvl): "
                "$ deq cnil (esort (lmax u u)) (esort u) $ =\n'(deq_sort (leveq_maxid));\n")
    results.append(("maxid_open", None))

    prelude = open(f"{HERE}/db.mm1").read()
    src = prelude + "\n" + "\n".join(thms)
    open("/tmp/cert_levels.mm1", "w").write(src)

    r = subprocess.run([MM0RS, "compile", "/tmp/cert_levels.mm1",
                        "/tmp/cert_levels.mmb"], capture_output=True, text=True)
    rs_ok = (r.returncode == 0)
    LG("mm0-rs rc=", r.returncode)
    if not rs_ok:
        LG("---stdout---"); LG(r.stdout[-4000:]); LG("---stderr---"); LG(r.stderr[-4000:])

    mmb = os.path.getsize("/tmp/cert_levels.mmb") if rs_ok else -1
    cc = subprocess.run([MM0C, "/tmp/cert_levels.mmb"], capture_output=True, text=True) if rs_ok else None
    cc_rc = cc.returncode if cc else -1
    LG("mm0-c rc=", cc_rc)

    with open("/tmp/levels_result.txt", "w") as fh:
        for label, n in results:
            fh.write("%s nodes=%s\n" % (label, n))
        fh.write("mm1_bytes=%d\n" % len(src))
        fh.write("mm0rs_rc=%d\n" % r.returncode)
        fh.write("mm0c_rc=%d\n" % cc_rc)
        fh.write("mmb_bytes=%d\n" % mmb)

    open("/tmp/levels.log", "w").write("\n".join(log) + "\n")
    print("done; rs_rc=%d cc_rc=%d" % (r.returncode, cc_rc))


if __name__ == "__main__":
    main()
