#!/usr/bin/env python3
"""The bbolt port's second mechanical pass (notes/bbolt-port-plan.md, §7, 2026-11-12): the file
parameter of the invariants is a `BFile` (path and inode, `Inv/Locks.lean`), so a file resource
named by a file parameter `p`/`K.p`/`path` takes its inode, and the v1 extension's `osMeta p q
(some m)` is `osMeta p.ino q m`. Rewrites the given files in place; prints what it changed.
Not idempotent on `.ino` (it never adds a second), safe to rerun.

usage: etc/fs-port/bbolt-bfile.py FILE...
"""
import re
import sys

RES = r'(osMeta|osBytes|osByte|osSlot0|osCell|osCells|osFdAt)'
# a file-parameter atom: p, K.p, w.p, path, p0 ... (not already followed by .ino/.path)
ATOM = r'(K\.p|p|path|p0|p\')'


def port(s: str) -> str:
    # `osMeta p q (some m)` -> `osMeta p.ino q m` (osMeta with an explicit GF too)
    s = re.sub(RES + r'( \(GF := GF\))?( \(L := L\))? ' + ATOM + r'(?![.\w\'])',
               lambda m: f'{m.group(1)}{m.group(2) or ""}{m.group(3) or ""} {m.group(4)}.ino', s)
    s = re.sub(r'(osMeta(?: \(GF := GF\))? \S+\.ino (?:\([^()]*\)|\S+)) \(some (\([^()]*\)|[^()\s]+)\)',
               r'\1 \2', s)
    s = re.sub(r'⟨' + ATOM + r', (true|false), (true|false)⟩', r'⟨\1.ino, \2, \3⟩', s)
    s = s.replace('List (w8 × Bool)', 'List ByteG').replace('(x : w8 × Bool)', '(x : ByteG)')
    return s


for f in sys.argv[1:]:
    s = open(f).read()
    t = port(s)
    if t != s:
        open(f, 'w').write(t)
        print(f'{f}: changed')
