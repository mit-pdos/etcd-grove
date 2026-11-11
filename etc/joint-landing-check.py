#!/usr/bin/env python3
"""The per-type stage's joint-landing condition (stage A and raft-entsize, one landing).

Stage A restates `swMsgBound_phys` (rafthttp/Transport.lean), a trust-boundary axiom known to be
false (aliased entries) and inconsistent in the logic in general; raft-entsize deletes it in the
same landing, deriving the bound from its tracked `sorry out_size`. This check refuses a tree whose
trust base still lists it: `axiom swMsgBound_phys` in etc/tcb-baseline.txt or in any
etc/tcb-collections/*.txt. It fails on the stage A branch until raft-entsize's Lean is in, which is
the point: stage A cannot land alone (etcd-grove-81, 2026-11-09).

    etc/joint-landing-check.py              exit 1 if the axiom is listed anywhere
    etc/joint-landing-check.py --selftest   the check refuses a baseline listing it and accepts one
                                            without it (scratch files in .lake/joint-landing/)
"""
import glob
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LINE = "axiom swMsgBound_phys"


def listed(paths):
    hits = []
    for p in paths:
        with open(p, encoding="utf-8") as f:
            if any(l.strip() == LINE for l in f):
                hits.append(os.path.relpath(p, ROOT))
    return hits


def trust_files():
    return [os.path.join(ROOT, "etc", "tcb-baseline.txt")] + sorted(
        glob.glob(os.path.join(ROOT, "etc", "tcb-collections", "*.txt")))


def main():
    if "--selftest" in sys.argv:
        d = os.path.join(ROOT, ".lake", "joint-landing")
        os.makedirs(d, exist_ok=True)
        bad, good = os.path.join(d, "with.txt"), os.path.join(d, "without.txt")
        open(bad, "w").write("axiom pbEntryC_reg\n" + LINE + "\n")
        open(good, "w").write("axiom pbEntryC_reg\nsorry out_size\n")
        ok = bool(listed([bad])) and not listed([good])
        print(f"joint-landing selftest: {'ok' if ok else 'FAILED'} (refuses a baseline listing "
              f"{LINE}, accepts one without it)")
        sys.exit(0 if ok else 1)
    hits = listed(trust_files())
    if hits:
        print(f"joint-landing: FAILED: {LINE} is still in the trust base ({', '.join(hits[:5])}"
              f"{', ...' if len(hits) > 5 else ''}): stage A lands only together with raft-entsize")
        sys.exit(1)
    print(f"joint-landing: ok ({LINE} in no baseline or collection)")


if __name__ == "__main__":
    main()
