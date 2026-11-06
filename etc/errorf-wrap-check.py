#!/usr/bin/env python3
"""Check that no proof learns a `fmt.Errorf` error's facts from Perennial's model.

Perennial's model of `fmt.Errorf` is `errors.New(format)`, which does not model `%w` (Go returns a
`*fmt.wrapError`; notes/decisions.md, "`fmt.Errorf` with `%w`: no fact from the model"). A fact
learned by stepping into the model is true of Go only when the lemma's statement says nothing
the model and Go disagree on (a post of `True`) or its premise excludes `%w`. The proofs that step
into it are the files below, each reviewed; a new one fails this check until it is reviewed and
added. The other specs of `fmt.Errorf` are axioms true of Go (`Spec/fmt/{Errorf,ErrorfPlain,
ErrorfWrap}.lean`). A cheap check, not a proof: it reads names, not terms.

usage: etc/errorf-wrap-check.py   (exit 1 on an unreviewed file)
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent

# file: why its model step is true of Go
REVIEWED = {
    'Proof/k8s_io/client_go/listers/apps/v1/ErrorfLabels.lean': 'post True',
    'Proof/k8s_io/client_go/tools/cache/ErrorfSet.lean': 'post True',
    'Proof/go_etcd_io/etcd/server/v3/storage/mvcc/Errorf.lean': 'premise (W8 37) ∉ format',
}

MODEL = re.compile(r'@! (_root_\.)?Perennial\.fmt\.Errorf\b')
STEP = re.compile(r'\bwp_start\b|\bwp_func_call\b')


def main():
    bad = []
    for f in sorted(ROOT.glob('**/*.lean')):
        rel = f.relative_to(ROOT)
        if rel.parts[0] in ('.lake', 'old', 'Code', 'GeneratedProof') or 'Code' in rel.parts[:2]:
            continue
        s = f.read_text()
        if MODEL.search(s) and STEP.search(s) and str(rel) not in REVIEWED:
            bad.append(rel)
    for rel in bad:
        print(f'errorf-wrap: {rel} steps into the `fmt.Errorf` model; review it '
              f'(a `%w` format?) and add it to REVIEWED', file=sys.stderr)
    if bad:
        return 1
    print(f'errorf-wrap: ok ({len(REVIEWED)} reviewed model steps)')
    return 0


if __name__ == '__main__':
    sys.exit(main())
