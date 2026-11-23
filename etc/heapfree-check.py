#!/usr/bin/env python3
"""The heap-free gate (phase 7 S2, O2; #24): the specs a service table holds reach no `HeapGS`.

Runs `etc/HeapFreeCheck.lean` on the roots of `etc/heapfree-roots.txt` (see its header and the
Lean file's) and exits with its status. Never builds: the listed modules' `.olean`s must be up to
date. `$LAKE_OPTS` is passed to `lake`.

    etc/heapfree-check.py
"""
import os, subprocess, sys
here = os.path.dirname(os.path.abspath(__file__))
mods, roots, negs = [], [], []
for line in open(os.path.join(here, 'heapfree-roots.txt')):
    line = line.split('#')[0].strip()
    if not line:
        continue
    if line.startswith('module '):
        mods.append(line.split()[1])
    elif line.startswith('neg '):
        negs.append(line.split()[1])
    else:
        roots.append(line)
cmd = ['lake'] + os.environ.get('LAKE_OPTS', '').split() + ['env', 'lean', '--run',
       os.path.join('etc', 'HeapFreeCheck.lean'), ','.join(mods)] + roots + ['--'] + negs
r = subprocess.run(cmd, cwd=os.path.dirname(here))
print('heapfree: ok (%d roots, %d negative tests)' % (len(roots), len(negs)) if r.returncode == 0
      else 'heapfree: FAILED')
sys.exit(r.returncode)
