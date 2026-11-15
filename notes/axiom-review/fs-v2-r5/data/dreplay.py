#!/usr/bin/env python3
"""fs-v2-r5 (c): replay a dm-log-writes log (data.sh) onto a copy of the base image, stopping after
every logged write; recover each image as a boot does (mount: the kernel replays the journal and
cleans up orphans; no e2fsck, which may change sizes the kernel would keep); check the file f
against the model's crash rule; then extend it and check the bytes past its old size read zeros.

The model's crash image of a file (Impl.lean, CrashFile with OsFile.ofDisk): a size between the
smallest and largest sizes since the last successful sync, each 512-byte sector one of its versions
since that sync, and the pages wholly past the size zeros (durable zeros), which only a later
extension or crash can show. Here the versions of a sector are taken from the file's whole states
since the sync (a superset of the sector's own versions: a state that did not change the sector
holds its previous bytes), so a violation reported is one; marks 'sync' in the log say which
syncs a crash point comes after (data.sh puts one after each fsync/fdatasync returned).

Usage: dreplay.py BASE.img LOGDEV SCENARIO WORKDIR
"""
import os, struct, subprocess, sys

FLUSH, FUA, DISCARD, MARK = 1, 2, 4, 8
base, logdev, sc, wd = sys.argv[1:5]
A =lambda n: b'a' * n
B = lambda n: b'b' * n
C = lambda n: b'c' * n
Dd = lambda n: b'd' * n
Z = lambda n: b'\0' * n
# each scenario: its states in order, 'sync' where a successful sync returned
SCEN = {
    'trunc-race': [A(8192), A(4096) + B(4096), A(100)],
    'shrink': [A(8192), A(100)],
    'falloc0': [A(4096), A(4096) + Z(12288)],
    'keep-past': [A(100), 'sync', A(100) + Z(8092) + B(1)],
    'gap': [A(100), A(100) + Z(4900) + B(10)],
    'seglog': [b'', Z(65536), Dd(8) + Z(65528), 'sync', Dd(8), Dd(8) + Z(65528)],
    'grow-sync': [A(16384), A(16384) + Z(16384), 'sync', A(16384) + B(4096) + Z(12288), 'sync',
                  C(4096) + A(12288) + B(4096) + Z(12288)],
}[sc]


def sh(*args, check=True):
    return subprocess.run(args, check=check, capture_output=True, text=True).stdout


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
            data = f.read(nr * ss) if not (flags & DISCARD) and nr else None
            yield (flags, sector * ss, nr * ss, data)
            off += ss * (1 + (0 if flags & DISCARD else nr))


def allowed(nsync):
    """The states since the nsync-th sync (the synced state first)."""
    st, k, cur = [], 0, None
    for s in SCEN:
        if s == 'sync':
            k += 1
            if k == nsync:
                st = [cur]
            continue
        cur = s
        if k >= nsync:
            st.append(s)
    return st


def check(img, ext, nsync):
    sts = allowed(nsync)
    if img is None:
        return 'no file f'
    lo, hi = min(len(s) for s in sts), max(len(s) for s in sts)
    if not lo <= len(img) <= hi:
        return 'size %d not in [%d, %d]' % (len(img), lo, hi)
    for n in range(0, len(img), 512):
        got = img[n:n + 512]
        if not any(s[n:n + len(got)].ljust(len(got), b'\0') == got for s in sts):
            return 'sector %d holds %r..., no version' % (n // 512, got[:16])
    if any(ext):
        return 'an extension past %d reads nonzero bytes at %d' % (
            len(img), len(img) + next(i for i, x in enumerate(ext) if x))
    return None


def snapshot(work):
    snap = os.path.join(wd, 'snap.img')
    sh('cp', '--sparse=always', work, snap)
    lo = sh('losetup', '--find', '--show', snap).strip()
    mnt = os.path.join(wd, 'snapmnt')
    os.makedirs(mnt, exist_ok=True)
    sh('mount', '-t', 'ext4', lo, mnt)
    p = os.path.join(mnt, 'f')
    img, ext = None, b''
    if os.path.exists(p):
        with open(p, 'rb') as g:
            img = g.read()
        ex = sh('debugfs', '-R', 'ex /f', lo, check=False)
        old = len(img)
        os.truncate(p, max(old, 1 << 17))
        with open(p, 'rb') as g:
            g.seek(old)
            ext = g.read()
    sh('umount', mnt)
    sh('losetup', '-d', lo)
    return img, ext


work = os.path.join(wd, 'work.img')
sh('cp', '--sparse=always', base, work)
nsync, npts, bad, seen = 0, 0, 0, {}
fd = os.open(work, os.O_RDWR)
for i, (fl, off, ln, data) in enumerate(entries(logdev)):
    if fl == 'mark':
        nsync += off == 'sync'
        continue
    if fl & DISCARD:
        os.pwrite(fd, b'\0' * ln, off)
    elif data:
        os.pwrite(fd, data, off)
    os.fsync(fd)
    img, ext = snapshot(work)
    npts += 1
    why = check(img, ext, nsync)
    key = None if img is None else (len(img), tuple(
        img[n:n + 512][:1] + bytes([len(set(img[n:n + 512]))]) for n in range(0, len(img), 512)))
    if why:
        bad += 1
        print('VIOLATION at entry %d (after %d syncs): %s' % (i, nsync, why))
    if key not in seen:
        seen[key] = (i, nsync, why)
os.close(fd)
print('%s: %d crash points (every logged write), %d distinct images, %d violations' % (
    sc, npts, len(seen), bad))


def show(img_key):
    if img_key is None:
        return 'no file'
    sz, secs = img_key
    runs, prev, cnt = [], None, 0
    for s in secs:
        ch = chr(s[0]) if 32 < s[0] < 127 else '%02x' % s[0]
        t = ch + ('' if s[1] == 1 else '*')
        if t == prev:
            cnt += 1
        else:
            if prev is not None:
                runs.append('%s x%d' % (prev, cnt))
            prev, cnt = t, 1
    if prev is not None:
        runs.append('%s x%d' % (prev, cnt))
    return 'size %d, sectors: %s' % (sz, ', '.join(runs))


for k, (i, ns, why) in sorted(seen.items(), key=lambda kv: kv[1][0]):
    print('  from entry %d (after %d syncs): %s%s' % (i, ns, show(k), '  <-- ' + why if why else ''))
