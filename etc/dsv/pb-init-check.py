#!/usr/bin/env python3
"""The condition of QuePaxa's protobuf axioms (`raxos.hyp.proto.{Marshal,Unmarshal}.wp_proof`,
review `notes/axiom-review/dsv-fix6/quepaxa-pb-2.md`, finding 1): no code of a package declaring
the kit's message types runs during that package's initialization before its generated `init()`.
`isPkgInit` of the declaring package, which `msg.marshalPre`/`unmarshalPre` ask, can be assembled
inside the package's own initializer before the generated `init` fills `file_*_msgTypes`, so a
`proto.Marshal` from a hand-written package-level variable initializer or `init()` there would be
proved safe and panic in Go. This checks that the hand-written (non-generated, non-test) Go files
of those packages declare no package-level `var` and no `func init`.

Usage: etc/dsv/pb-init-check.py   (exit 1 on a violation)
"""
import os, re, sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..')
PKGS = [os.path.join('examples', 'dsverify', 'quepaxa', 'proto', 'client'),
        os.path.join('examples', 'dsverify', 'quepaxa', 'replica', 'src')]
BAD = re.compile(r'^(var\b|func\s+init\s*\()')

bad = []
for pkg in PKGS:
    d = os.path.join(ROOT, pkg)
    for f in sorted(os.listdir(d)):
        if not f.endswith('.go') or f.endswith('_test.go') or f.endswith('.pb.go'):
            continue
        with open(os.path.join(d, f)) as h:
            for n, line in enumerate(h, 1):
                if BAD.match(line):
                    bad.append(f'{pkg}/{f}:{n}: {line.rstrip()}')
for b in bad:
    print(f'pb-init-check: package-level initializer in a message package: {b}')
if bad:
    sys.exit(1)
print('pb-init-check: ok')
