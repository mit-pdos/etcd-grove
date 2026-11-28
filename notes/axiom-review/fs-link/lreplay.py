#!/usr/bin/env python3
"""fs-link: replay a dm-log-writes log onto a copy of the base image, stop at every flush or FUA
entry (and at the end), recover the image there as a reboot would (a kernel mount replays the
journal and the orphan list), mount it read-only, and check the snapshot directory against the
SaveDBFrom axiom's link assumptions (linkops.go's scenarios; examples/osfs/semantics/meta_link_*.go):

  (ii)  0000000000000005.snap.db is absent, or holds the whole synced stream (never a prefix,
        never another file's bytes); in snapsave-exist it is always the old file;
  (iii) tmp1 and the .snap.db may both be there, then as one inode (nlink 2);
  and after the mark of the returned directory fsync: the .snap.db with the stream, no tmp1.

Marks (put after a call returned) say which calls a crash point comes after.
The log parsing is fs-v2-r5/meta/replay.py's (dm-log-writes' format, drivers/md/dm-log-writes.c).

Usage: lreplay.py BASE.img LOGDEV SCENARIO OPS.txt WORKDIR
"""
import os, struct, subprocess, sys

FLUSH, FUA, DISCARD, MARK = 1, 2, 4, 8
base, logdev, sc, opsf, wd = sys.argv[1:6]
FN = '0000000000000005.snap.db'
DATA = b'snapdata' * 8192  # linkops.go's Data()


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


def snapshot(work):
    """The recovered image's root: name -> (ino, nlink, bytes)."""
    snap = os.path.join(wd, 'snap.img')
    sh('cp', '--sparse=always', work, snap)
    lo = sh('losetup', '--find', '--show', snap).strip()
    mnt = os.path.join(wd, 'snapmnt')
    os.makedirs(mnt, exist_ok=True)
    sh('mount', '-t', 'ext4', lo, mnt)
    sh('umount', mnt)
    sh('mount', '-t', 'ext4', '-o', 'ro', lo, mnt)
    tree = {}
    for n in os.listdir(mnt):
        if n == 'lost+found':
            continue
        p = os.path.join(mnt, n)
        st = os.lstat(p)
        with open(p, 'rb') as g:
            tree[n] = (st.st_ino, st.st_nlink, g.read())
    sh('umount', mnt)
    sh('losetup', '-d', lo)
    return tree


def check(tree, marks):
    """None if the image is one the axiom allows, else why not."""
    f, t = tree.get(FN), tree.get('tmp1')
    extra = set(tree) - {FN, 'tmp1'}
    if extra:
        return 'other names: %r' % sorted(extra)
    if sc == 'snapsave-exist':
        if f is None or f[2] != b'old' or f[1] != 1:
            return 'the existing file changed: %r' % (f and (f[1], f[2][:16]))
        if t is not None and t[0] == f[0]:
            return 'tmp1 is the existing file'
    else:
        if f is not None and f[2] != DATA:
            return '(ii) %s holds %d bytes, not the stream' % (FN, len(f[2]))
        if f is not None and t is not None and (f[0] != t[0] or f[1] != 2 or t[1] != 2):
            return '(iii) both names but not one inode: %r %r' % (f[:2], t[:2])
        if f is not None and t is None and f[1] != 1:
            return 'nlink %d with one name' % f[1]
    if 'fsyncdir:root' in marks:
        if t is not None:
            return 'after the directory fsync: tmp1 still there'
        if sc == 'snapsave' and f is None:
            return 'after the directory fsync: no %s' % FN
    return None


def describe(tree):
    out = []
    for n in sorted(tree):
        ino, nl, b = tree[n]
        what = 'stream' if b == DATA else ('old' if b == b'old' else '%d bytes' % len(b))
        out.append('%s(ino %d, nlink %d, %s)' % (n, ino, nl, what))
    return ' '.join(out) or 'empty'


work = os.path.join(wd, 'work.img')
sh('cp', '--sparse=always', base, work)
marks, npts, bad, seen, per = [], 0, 0, {}, {}
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
        tree = snapshot(work)
        npts += 1
        why = check(tree, marks)
        key = describe(tree)
        seen.setdefault(key, (i, list(marks), why))
        last = marks[-1] if marks else '-'
        per.setdefault(last, {}).setdefault(key, 0)
        per[last][key] += 1
        if why:
            bad += 1
            print('VIOLATION at entry %d (after %s): %s' % (i, marks[-1:], why))
os.close(fd)
print('%s: %d crash points (flush/FUA entries), %d distinct images, %d violations' % (
    sc, npts, len(seen), bad))
for key, (i, mk, why) in sorted(seen.items(), key=lambda kv: kv[1][0]):
    print('  from entry %d (after mark %s): %s%s' % (i, mk[-1] if mk else '-', key,
                                                   '  <-- ' + why if why else ''))
print('crash points by the last mark before them (image: count):')
for mk, imgs in per.items():
    print('  after %s: %d points' % (mk, sum(imgs.values())))
    for key, n in imgs.items():
        print('    %d x %s' % (n, key))
