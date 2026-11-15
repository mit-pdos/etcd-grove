#!/usr/bin/env python3
"""fs-v2-r6 (d): device write reordering between flushes. Round 5's replays (fs-v2-r5/meta/replay.py,
fs-v2-r5/data/dreplay.py) rebuilt the disk from a dm-log-writes log in completion order. A device
that honours flushes (C's device clause) may persist any subset of the writes completed since the
last cache flush (a FUA write once it completes). This replays the same logs with that freedom: at
each crash point (before each flush/FUA entry, and at the end), the image holds every write before
the last PREFLUSH entry, every FUA write, and a random subset of the other writes since (applied in
log order), R subsets per point plus "none of them"; each image is recovered by a kernel mount and
checked with round 5's checker for the scenario.

Usage: reorder.py meta|data BASE.img LOGDEV SCENARIO [OPS.txt] WORKDIR [R] [SEED]
"""
import os, random, sys

HERE = os.path.dirname(os.path.abspath(__file__))
R5 = os.path.join(HERE, '..', '..', 'fs-v2-r5')
kind = sys.argv[1]
if kind == 'meta':
    base, logdev, sc, opsf, wd = sys.argv[2:7]
    rest = sys.argv[7:]
    src = os.path.join(R5, 'meta', 'replay.py')
    sys.argv = [src, base, logdev, sc, opsf, wd]
else:
    base, logdev, sc, wd = sys.argv[2:6]
    rest = sys.argv[6:]
    src = os.path.join(R5, 'data', 'dreplay.py')
    sys.argv = [src, base, logdev, sc, wd]
R = int(rest[0]) if rest else 6
random.seed(int(rest[1]) if len(rest) > 1 else 1)
text = open(src).read()
pre = text[:text.index("work = os.path.join(wd, 'work.img')")]
g = {'__name__': 'r5', '__file__': src}
exec(compile(pre, src, 'exec'), g)

ents = list(g['entries'](logdev))
FLUSH, FUA, DISCARD = g['FLUSH'], g['FUA'], g['DISCARD']


def build(upto, chosen):
    work = os.path.join(wd, 'work.img')
    g['sh']('cp', '--sparse=always', base, work)
    fd = os.open(work, os.O_RDWR)
    for i in range(upto):
        fl, off, ln, data = ents[i]
        if fl == 'mark' or i not in chosen:
            continue
        if fl & DISCARD:
            os.pwrite(fd, b'\0' * ln, off)
        elif data:
            os.pwrite(fd, data, off)
    os.fsync(fd)
    os.close(fd)
    return work


points = [i for i, e in enumerate(ents) if e[0] != 'mark' and e[0] & (FLUSH | FUA)] + [len(ents)]
npts, nimg, bad, seen = 0, 0, 0, set()
for c in points:
    lastflush = max([i for i in range(c) if ents[i][0] != 'mark' and ents[i][0] & FLUSH] + [0])
    sure = {i for i in range(c) if ents[i][0] != 'mark' and (i < lastflush or ents[i][0] & FUA)}
    free = [i for i in range(lastflush, c) if ents[i][0] != 'mark' and i not in sure]
    marks = [e[1] for e in ents[:c] if e[0] == 'mark']
    subsets = [frozenset()] + [frozenset(i for i in free if random.random() < 0.5) for _ in range(R)]
    npts += 1
    for sub in set(subsets):
        if not free and sub:
            continue
        work = build(c, sure | sub)
        nimg += 1
        if kind == 'meta':
            tree, _ = g['snapshot'](work, c)
            why = g['check'](tree, marks)
            key = repr(sorted((p, v if v == 'dir' else v.hex()) for p, v in tree.items()))
        else:
            img, ext = g['snapshot'](work)
            why = g['check'](img, ext, sum(1 for m in marks if m == 'sync'))
            key = repr(None if img is None else (len(img), img[:8], len(set(img))))
        seen.add(key)
        if why:
            bad += 1
            print('VIOLATION at point %d (%d free writes, %d kept): %s' % (c, len(free), len(sub), why))
print('%s (%s, reordered): %d crash points, %d images, %d distinct, %d violations' % (
    sc, kind, npts, nimg, len(seen), bad))
