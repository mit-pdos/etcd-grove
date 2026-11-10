#!/usr/bin/env python3
"""fs-v2-r5 (b): replay a dm-log-writes log onto a copy of the base image, stop at every flush or
FUA entry (and at the end), recover the image there as a reboot would (e2fsck replays the journal),
mount it read-only, and check the tree against the model's journal order for the scenario
(metaops.go). Marks (put after a call returned) say which calls a crash point comes after.

Usage: replay.py BASE.img LOGDEV SCENARIO OPS.txt WORKDIR
dm-log-writes' format: drivers/md/dm-log-writes.c (v7.0): a super block (magic, version,
nr_entries, sectorsize) at 0; entries from sector 1 (in sectorsize units), each a header block
(sector, nr_sectors, flags, data_len; a mark's name inline) followed by nr_sectors blocks of data.
"""
import os, struct, subprocess, sys

FLUSH, FUA, DISCARD, MARK = 1, 2, 4, 8
base, logdev, sc, opsf, wd = sys.argv[1:6]


def sh(*a, check=True):
    return subprocess.run(a, check=check, capture_output=True, text=True).stdout


def entries(path):
    with open(path, 'rb') as f:
        magic, ver, n, ss = struct.unpack('<QQQI', f.read(28))
        assert magic == 0x6a736677736872, hex(magic)
        off = ss
        for _ in range(n):
            f.seek(off)
            hdr = f.read(ss)
            sector, nr, flags, dlen = struct.unpack('<QQQQ', hdr[:32])
            if flags & MARK:
                yield ('mark', hdr[32:32 + dlen].rstrip(b'\0').decode(), None, None)
                off += ss
                continue
            data = None
            if not (flags & DISCARD) and nr:
                data = f.read(nr * ss)
            yield (flags, sector * ss, nr * ss, data)
            off += ss * (1 + (0 if flags & DISCARD else nr))


def snapshot(work, k):
    snap = os.path.join(wd, 'snap.img')
    sh('cp', '--sparse=always', work, snap)
    lo = sh('losetup', '--find', '--show', snap).strip()
    r = subprocess.run(['e2fsck', '-fy', lo], capture_output=True, text=True)
    mnt = os.path.join(wd, 'snapmnt')
    os.makedirs(mnt, exist_ok=True)
    sh('mount', '-t', 'ext4', '-o', 'ro', lo, mnt)
    tree = {}
    for dp, dns, fns in os.walk(mnt):
        rel = os.path.relpath(dp, mnt)
        if rel.startswith('lost+found'):
            continue
        for d in dns:
            if d != 'lost+found':
                tree[os.path.normpath(os.path.join(rel, d))] = 'dir'
        for fn in fns:
            with open(os.path.join(dp, fn), 'rb') as g:
                tree[os.path.normpath(os.path.join(rel, fn))] = g.read(64)
    sh('umount', mnt)
    sh('losetup', '-d', lo)
    return tree, r.returncode


def ops():
    res = []
    for line in open(opsf):
        if line.startswith('OP '):
            _, name, b, e, _ = line.split(' ', 4)
            res.append((name, int(b), int(e)))
    return res


DATA = bytes([0xde, 0xad, 0xbe, 0xef, 0x01, 0x23, 0x45, 0x67])


def names(tree, d):
    pre = '' if d == '.' else d + '/'
    return {p[len(pre):] for p in tree if p.startswith(pre) and '/' not in p[len(pre):]}


def check(tree, marks):
    """The model's verdict on one crash image: None if allowed, else why not."""
    top = names(tree, '.')
    if sc == 'segdir':
        if 'seg' in top and 'seg.tmp' in top:
            return 'seg and seg.tmp both'
        if 'seg' in top and tree['seg'] != DATA:
            return 'seg without its data: %r' % tree['seg']
        if 'fsyncdir:root' in marks and top != {'seg'}:
            return 'after the directory fsync: %r' % top
    elif sc == 'dirswap':
        if 'wal' in top and 'wal.tmp' in top:
            return 'wal and wal.tmp both'
        if 'wal' in top and tree.get('wal/seg') != DATA:
            return 'wal without seg holding the data: %r' % names(tree, 'wal')
        if 'fsyncdir:root' in marks and 'wal' not in top:
            return 'after the directory fsync, no wal'
    elif sc == 'crashlog':
        b = tree.get('log')
        if b is not None and len(b) > 8 and b[8] != 0 and b[:8] != DATA:
            return 'flag without data: %r' % b
        if 'fdatasync:2' in marks and b is not None and b != DATA + b'\x01':
            return 'after the second fdatasync: %r' % b
    elif sc == 'replace':
        t = tree.get('target')
        if t not in (b'old.....', b'new.....'):
            return 'target is %r' % t
        if 'tmp' in top and t != b'old.....':
            return 'tmp and the new target both'
        if 'fsyncdir:root' in marks and t != b'new.....':
            return 'after the directory fsync, target %r' % t
    elif sc in ('overlap', 'xrename'):
        return check_threads(tree)
    return None


def check_threads(tree):
    """Per directory, the kept calls are a prefix of that directory's calls (they all lock it);
    across directories, a kept call keeps every call that returned before it began (Follows'
    y < x.start, here by the clock: a call that returned before another began took effect
    before it)."""
    L = ops()
    kept = {}
    for d in ('a', 'b'):
        seq = [o for o in L if o[0].split(':')[1] == d]
        if sc == 'overlap':
            ns = names(tree, d)
            m = 0
            while 'y%d' % m in ns:
                m += 1
            k = 2 * m + (1 if 'x%d' % m in ns else 0)
            want = {'y%d' % i for i in range(m)} | ({'x%d' % m} if k % 2 else set())
            if ns != want:
                return 'dir %s is not a prefix: %d names, prefix %d' % (d, len(ns), k)
        else:
            ns = names(tree, 'c')
            m = 0
            while '%s%d' % (d, m) in ns:
                m += 1
            if {x for x in ns if x.startswith(d)} != {'%s%d' % (d, i) for i in range(m)}:
                return 'c holds a non-prefix of %s' % d
            left = names(tree, d)
            if left != {'f%d' % i for i in range(m, 400)}:
                return '%s holds %d names, c %d of its' % (d, len(left), m)
            k = m
        kept[d] = (seq, k)
    for d, e in (('a', 'b'), ('b', 'a')):
        seq, k = kept[d]
        if k == 0:
            continue
        last_begin = seq[k - 1][1]
        oseq, ok = kept[e]
        need = sum(1 for o in oseq if o[2] < last_begin)
        if need > ok:
            return '%s keeps %d calls; %s returned %d calls before the last began, kept %d' % (
                d, k, e, need, ok)
    return None


work = os.path.join(wd, 'work.img')
sh('cp', '--sparse=always', base, work)
marks, npts, bad, seen = [], 0, 0, {}
fd = os.open(work, os.O_RDWR)
for i, (fl, off, ln, data) in enumerate(entries(logdev)):
    if fl == 'mark':
        marks.append(off)
        continue
    if fl & DISCARD:
        os.pwrite(fd, b'\0' * ln, off)
    elif data:
        os.pwrite(fd, data, off)
    if fl & (FLUSH | FUA):
        os.fsync(fd)
        tree, rc = snapshot(work, i)
        npts += 1
        why = check(tree, marks)
        key = repr(sorted((p, v if v == 'dir' else v.hex()) for p, v in tree.items())
                   if sc not in ('overlap', 'xrename') else
                   [len(names(tree, d)) for d in ('a', 'b', 'c')])
        seen.setdefault(key, (i, list(marks), why))
        if why:
            bad += 1
            print('VIOLATION at entry %d (after %s): %s' % (i, marks[-1:] , why))
os.close(fd)
print('%s: %d crash points (flush/FUA entries), %d distinct images, %d violations' % (
    sc, npts, len(seen), bad))
for key, (i, mk, why) in sorted(seen.items(), key=lambda kv: kv[1][0]):
    print('  from entry %d (after mark %s): %s%s' % (i, mk[-1] if mk else '-', key[:300],
                                                   '  <-- ' + why if why else ''))
