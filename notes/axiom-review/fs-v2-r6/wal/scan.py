#!/usr/bin/env python3
"""fs-v2-r6 wal: check every logged write of an etcd WAL page, and recover and check crash images.

The log is dm-log-writes' (../e2e/scan.py: every write is a crash point; the base plus the log's
writes up to and including it is a state a crash of a flush-honouring device can leave). The WAL
only appends, into a preallocated segment (zeros), and every page reaches its final content
(FINAL, the file after the run: Close synced it). So every version of page p etcd hands the kernel
is F[0:k] + zeros, F the page's final content, k the end of a write() in the page: the end of a
Save that synced (the encoder flushes only in sync(), or at a page boundary when its buffer is
full). A logged write of the page is classified:

  ok          F[0:k] + zeros with k a sync point (the end of a State/Snapshot record) or 4096;
  cut-record  F[0:k] + zeros, k a record boundary but not a sync point;
  cut-mid     F[0:k] + zeros, k inside a record: a tear (sub-classes: k a multiple of 512 or not:
              a mixed sector);
  mixed       not of that shape (a byte differs from F and from 0 below the zero suffix: two
              versions mixed, or stale data).

Crash images: every point whose write is not ok (the first MAXIMG), and NSAMPLE ordinary points
spread over the log (a check of the pipeline and of durability). Each is built, recovered as a boot
does (a kernel mount and an unmount: c_recover), mounted read-write, and every WAL checked by
`walw check` (etcd's bootstrap: Open, ReadAll, Repair on io.ErrUnexpectedEOF) with the last index
whose synced Save had returned (the writer's last mark "s<j>:<idx>" before the point).

Usage: scan.py BASE.img LOG MAPS NW WORKDIR [MAXIMG] [NSAMPLE] [WALW]
Env: ATTR=content attributes a logged block to the final pages that begin with its first 64 bytes
(nonzero) instead of by the final block map: for runs with restarts, whose ZeroToEnd (truncate +
fallocate) moves the blocks after the tail; blocks that start with 64 zero bytes are then skipped.
"""
import os, re, struct, subprocess, sys

FLUSH, FUA, DISCARD, MARK = 1, 2, 4, 8
base, logf, maps, nw, wd = sys.argv[1:6]
nw = int(nw)
maxim = int(sys.argv[6]) if len(sys.argv) > 6 else 50
nsample = int(sys.argv[7]) if len(sys.argv) > 7 else 40
walw = sys.argv[8] if len(sys.argv) > 8 else None
STATE, SNAP = 3, 5


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


def records(F):
    """[(start, end, type)] of the WAL records of the final file F (frame: 8-byte length, the low
    56 bits the record's size, the top byte 0x80|pad; record: protobuf, field 1 the type)."""
    out, off = [], 0
    while off + 8 <= len(F):
        l, = struct.unpack('<Q', F[off:off + 8])
        if l == 0:
            break
        rb = l & ((1 << 56) - 1)
        pad = (l >> 56) & 7 if l >> 63 else 0
        end = off + 8 + rb + pad
        typ = F[off + 9] if F[off + 8] == 0x08 else -1
        out.append((off, end, typ))
        off = end
    return out


# the WAL files: final content, block map, record boundaries and sync points
phys = {}  # physical block -> (writer, logical page)
final, syncpts, bounds, recs, paths = [], [], [], [], []
for j in range(nw):
    F = open(os.path.join(maps, 'final.%d' % j), 'rb').read()
    final.append(F)
    nbl = 0
    for line in open(os.path.join(maps, 'ex.%d' % j)):  # debugfs `ex`: the extent tree's leaves
        m = re.match(r'\s*\d+/\s*\d+\s+\d+/\s*\d+\s+(\d+)\s*-\s*(\d+)\s+(\d+)\s*-\s*(\d+)\s', line)
        if m:
            l0, l1, p0, _ = map(int, m.groups())
            for x in range(l1 - l0 + 1):
                phys[p0 + x] = (j, l0 + x)
            nbl += l1 - l0 + 1
    rs = records(F)
    recs.append(rs)
    syncpts.append({e for _, e, t in rs if t in (STATE, SNAP)})
    bounds.append({s for s, _, _ in rs} | {e for _, e, _ in rs})
    paths.append(open(os.path.join(maps, 'path.%d' % j)).read().strip())
    print('w%d: %d bytes of records, %d records, %d blocks mapped' % (j, rs[-1][1] if rs else 0, len(rs), nbl))


content = os.environ.get('ATTR') == 'content'
index = {}
if content:
    for j in range(nw):
        F = final[j]
        for lp in range(len(F) // 4096):
            h = F[lp * 4096:lp * 4096 + 64]
            if h.count(0) != 64:
                index.setdefault(h, []).append((j, lp))


def classify(j, lp, P):
    F = final[j][lp * 4096:(lp + 1) * 4096]
    if P == F:
        return 'ok', 4096
    z = len(P.rstrip(b'\0'))
    if P[:z] != F[:z]:
        diff = [i for i in range(z) if P[i] != F[i]]
        return 'mixed', (diff[0], diff[-1], len(diff), z)
    # the cut may be anywhere in F's zero run from z on (padding, a length's high bytes)
    c, pos = z, lp * 4096 + z
    cands = [z]
    while c < 4096 and F[c] == 0:
        c += 1
        cands.append(c)
    if any(lp * 4096 + x in syncpts[j] for x in cands):
        return 'ok', z
    if any(lp * 4096 + x in bounds[j] for x in cands):
        return 'cut-record', z
    return 'cut-mid' + ('' if z % 512 == 0 else ' MIXED-SECTOR'), z


def rec_at(j, off):
    for s, e, t in recs[j]:
        if s <= off < e:
            return s, e, t
    return None


# pass 1
stats = {}
odd = []  # (index, writer, page, class, info)
nent = npg = 0
nmarks = 0
for i, e in enumerate(entries(logf)):
    fl, off, ln, data = e
    nent += 1
    if fl == 'mark':
        nmarks += 1
        continue
    if data is None:
        continue
    for o in range(off - off % 4096, off + ln, 4096):
        if o < off or o + 4096 > off + ln:
            continue
        P = data[o - off:o - off + 4096]
        if content:
            # by content (a restart's truncate + fallocate moves the blocks after the tail): the
            # final pages that start as this block does; the best class among them
            cs = index.get(P[:64], ())
            if not cs:
                continue
            jp, cl, info = min(((c,) + classify(c[0], c[1], P) for c in cs), key=lambda x: x[1] != 'ok')
        else:
            jp = phys.get(o // 4096)
            if jp is None:
                continue
            cl, info = classify(jp[0], jp[1], P)
        npg += 1
        stats[cl] = stats.get(cl, 0) + 1
        if cl != 'ok':
            odd.append((i, jp[0], jp[1], cl, info))
print('log: %d entries (%d marks), %d writes of a WAL page: %s' % (nent, nmarks, npg, stats))
for i, j, lp, cl, info in odd[:200]:
    extra = ''
    if cl.startswith('cut'):
        r = rec_at(j, lp * 4096 + info)
        extra = ' (record %s)' % (r,)
    print('ODD write %d: w%d page %d (file offset %d): %s %s%s' % (i, j, lp, lp * 4096, cl, info, extra))

# pass 2
nlog = nent
todo = {i: 'odd ' + cl for i, _, _, cl, _ in odd[:maxim]}
for k in range(1, nsample + 1):
    todo.setdefault(nlog * k // (nsample + 1), 'sample')
order = sorted(todo)
results = {}
if order and walw:
    work = os.path.join(wd, 'work.img')
    sh('cp', '--sparse=always', base, work)
    fd = os.open(work, os.O_RDWR)
    synced = [0] * nw
    k = 0
    for i, e in enumerate(entries(logf)):
        if k >= len(order):
            break
        fl, off, ln, data = e
        if fl == 'mark':
            if off.startswith('s') and ':' in off:
                a, b = off[1:].split(':')
                synced[int(a)] = int(b)
        elif fl & DISCARD:
            os.pwrite(fd, b'\0' * ln, off)
        elif data:
            os.pwrite(fd, data, off)
        if i == order[k]:
            k += 1
            os.fsync(fd)
            snap = os.path.join(wd, 'crash.%d.img' % i)
            sh('cp', '--sparse=always', work, snap)
            lo = sh('losetup', '--find', '--show', snap).stdout.strip()
            mnt = os.path.join(wd, 'crashmnt')
            os.makedirs(mnt, exist_ok=True)
            sh('mount', '-t', 'ext4', lo, mnt)  # c_recover: journal replay, orphan cleanup
            sh('umount', mnt)
            sh('mount', '-t', 'ext4', lo, mnt)
            out = []
            for j in range(nw):
                d = os.path.join(mnt, os.path.dirname(paths[j]))
                if not os.path.isdir(d):
                    out.append('w%d: no WAL (synced %d)' % (j, synced[j]))
                    continue
                r = subprocess.run([walw, 'check', d, str(synced[j])], capture_output=True, text=True)
                line = (r.stdout + r.stderr).strip().splitlines()
                line = line[-1] if line else ''
                out.append('w%d: %s' % (j, line))
                kind = line.split(':')[0].split(' ')[0] + (' LOSS' if 'LOSS' in line else '') + (' BAD' if 'BAD' in line else '')
                results[kind] = results.get(kind, 0) + 1
            print('IMAGE after write %d (%s): %s' % (i, todo[i], ' | '.join(out)))
            sh('umount', mnt)
            sh('losetup', '-d', lo)
            if not os.environ.get('KEEP') or todo[i] == 'sample':
                os.unlink(snap)
    os.close(fd)
    os.unlink(work)
print('images: %d, WAL checks: %s' % (len(order), results))
