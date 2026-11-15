#!/usr/bin/env python3
"""fs-v2-r6 e2e: find torn crash images in a dm-log-writes log, recover them, run the application.

Every write in the log is a crash point: the disk holding the base image plus the log's writes up
to and including it (dm-log-writes logs writes in completion order, so this is a state a crash of a
flush-honouring device can leave). The block of page 0 of each file f<j> (BLOCKS, 4 KiB block
numbers) is checked in every write that covers it: torn if it holds more than one byte value. For
the first MAXIMG torn points the image is built, recovered as a boot does (a kernel mount, which
replays the journal, then an unmount: c_recover of fs-config/mkfs-mount.sh), mounted read-only, page
0 of each file read through the filesystem, and BOOT (boot.go) run on it.

Usage: scan.py BASE.img LOGFILE BLOCKS WORKDIR SKEW [MAXIMG] [BOOT]
  BLOCKS: comma-separated block numbers of f0's, f1's, ... page 0
Prints one line per torn write (the cut and the values) and a summary.
"""
import os, struct, subprocess, sys

FLUSH, FUA, DISCARD, MARK = 1, 2, 4, 8
base, logf, blocks, wd, skew = sys.argv[1:6]
maxim = int(sys.argv[6]) if len(sys.argv) > 6 else 3
boot = sys.argv[7] if len(sys.argv) > 7 else None
blocks = [int(b) for b in blocks.split(',')]
bfile = {b * 4096: j for j, b in enumerate(blocks)}
skew = int(skew)
want_cut = (4096 - skew) % 4096


def sh(*a, check=True):
    return subprocess.run(a, check=check, capture_output=True, text=True)


def entries(path):
    with open(path, 'rb', buffering=1 << 24) as f:
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


def segments(pg):
    """[(start, value)] of the runs of equal bytes."""
    segs, i = [], 0
    while i < 4096:
        v = pg[i]
        j = i
        while j < 4096 and pg[j] == v:
            j += 1
        segs.append((i, v))
        i = j
    return segs


def nxt(b):
    """The value of the write after one of value b (tearw: 1..255, cycling)."""
    return b % 255 + 1


def mixed_sector(segs):
    """Does a run boundary fall inside a 512-byte sector (a sector holding two values: never a
    version the sector had, which the semantics' crash rule excludes)?"""
    return any(c % 512 for c, _ in segs[1:])


def classify(segs):
    return ('MIXED-SECTOR ' if mixed_sector(segs) else 'sector-aligned ') + classify1(segs)


def classify1(segs):
    if len(segs) == 2:
        (_, a), (c, b) = segs
        rel = 'new prefix' if a == nxt(b) else ('old prefix' if b == nxt(a) else 'values %d, %d' % (a, b))
        src = 'cut at the source page boundary' if c == want_cut else 'cut elsewhere'
        return '2 runs, cut %d (%s, %s)' % (c, rel, src)
    return '%d runs' % len(segs)


# pass 1: find the torn writes
torn = []  # (index, file, segs)
pg0 = nw = ne = 0
for i, e in enumerate(entries(logf)):
    fl, off, ln, data = e
    ne += 1
    if fl == 'mark' or data is None:
        continue
    nw += 1
    for o in range(off - off % 4096, off + ln, 4096):
        if o in bfile and o >= off and o + 4096 <= off + ln:
            pg0 += 1
            pg = data[o - off:o - off + 4096]
            if pg.count(pg[0]) != 4096:
                torn.append((i, bfile[o], segments(pg)))
ms = [t for t in torn if mixed_sector(t[2])]
atb = [t for t in torn if len(t[2]) == 2 and t[2][1][0] == want_cut and t[2][0][1] == nxt(t[2][1][1])]
print('log: %d entries, %d writes, %d writes of a page 0, %d torn, %d with a mixed sector, '
      '%d new-prefix cuts at the source page boundary (%d)' % (ne, nw, pg0, len(torn), len(ms), len(atb), want_cut))
for i, j, segs in torn:
    print('TORN write %d: f%d page 0: %s; runs %s' % (i, j, classify(segs), segs[:6]))

# pass 2: build, recover and check the first MAXIMG torn crash images with a mixed sector, the
# source-boundary ones first
pick = atb + [t for t in ms if t not in atb]
todo = sorted({i for i, _, _ in pick[:maxim]})
if todo:
    work = os.path.join(wd, 'work.img')
    sh('cp', '--sparse=always', base, work)
    fd = os.open(work, os.O_RDWR)
    k = 0
    for i, e in enumerate(entries(logf)):
        if k >= len(todo):
            break
        fl, off, ln, data = e
        if fl != 'mark':
            if fl & DISCARD:
                os.pwrite(fd, b'\0' * ln, off)
            elif data:
                os.pwrite(fd, data, off)
        if i == todo[k]:
            k += 1
            os.fsync(fd)
            snap = os.path.join(wd, 'crash.%d.img' % i)
            sh('cp', '--sparse=always', work, snap)
            lo = sh('losetup', '--find', '--show', snap).stdout.strip()
            mnt = os.path.join(wd, 'crashmnt')
            os.makedirs(mnt, exist_ok=True)
            # c_recover: a kernel mount (journal replay, orphan cleanup) and an unmount
            sh('mount', '-t', 'ext4', lo, mnt)
            sh('umount', mnt)
            sh('mount', '-t', 'ext4', '-o', 'ro', lo, mnt)
            out = []
            for j in range(len(blocks)):
                with open(os.path.join(mnt, 'f%d' % j), 'rb') as g:
                    pg = g.read()
                s = segments(pg) if len(pg) == 4096 else None
                out.append('f%d %s' % (j, 'size %d' % len(pg) if s is None else
                                       ('one value %#04x' % s[0][1] if len(s) == 1 else 'TORN ' + classify(s))))
            print('IMAGE after write %d, recovered: %s' % (i, '; '.join(out)))
            if boot:
                r = subprocess.run(['sudo', '-u', os.environ.get('SUDO_USER', 'nobody'), boot, mnt, str(len(blocks))],
                                   capture_output=True, text=True)
                tail = (r.stdout + r.stderr).strip().splitlines()
                print('  boot exit %d: %s' % (r.returncode, ' | '.join(l for l in tail if 'panic' in l or 'ok' in l or 'torn' in l)[:600]))
            sh('umount', mnt)
            sh('losetup', '-d', lo)
            keep = os.environ.get('KEEP')
            if not keep:
                os.unlink(snap)
    os.close(fd)
    os.unlink(work)
