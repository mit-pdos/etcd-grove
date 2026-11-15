# fs-v2-r6 wal: can etcd's real WAL fail to recover after a crash on C, a torn tail sector read as corruption?

**Date:** 2026-11-11. **Result: not caught end to end; the failure is real if a mid-sector cut
reaches the disk, and one of the two ways there is present in etcd's WAL.** On configuration C
(`../../fs-config/README.md`; every filesystem made by `mkfs-mount.sh`, passing `check.sh`, crash
images recovered by a kernel mount as `c_recover`), etcd's WAL (`go.etcd.io/etcd/server/v3/storage/wal`,
upstream `main` 6974f522338b, 2026-11-10, go1.27.3) recovered every crash image checked: 1,616 WAL
bootstraps on 202 images of 5 logged runs, 0.82 M Saves (1.10 M page writes logged and
classified), no unrecoverable image, no synced entry lost. But:

- **(A) The source page boundary.** The encoder's `PageWriter` flushes its buffer (`make([]byte,
  128K+4096)`: a large object, page-aligned) to the file's current offset, mid-page after nearly
  every Save; so the buffer's page boundaries land mid-page in the file, and a copy cut there (the
  e2e's mechanism A: a source page under migration) leaves the file page torn mid-sector with zeros
  after. The WAL's decoder (`decoder.go`, `isTornEntry`) calls a bad last record torn only if one of
  its sectors is all zero; otherwise `ReadAll` returns a CRC mismatch or a protobuf error, and
  bootstrap (`etcdserver/bootstrap.go`, `openWALFromSnapshot`) repairs only `io.ErrUnexpectedEOF`:
  the member exits ("failed to read WAL, cannot be repaired"). Of the images such a cut leaves,
  17-24 % fail so (`tornsim`, below). Observed in the page cache once in ~10^7 WAL writes under
  forced compaction (cut at in-page 24); never written back torn (0 writebacks inside a torn
  window).
- **(B) No stable pages.** In steady state it cannot happen: every rewrite of the tail page follows
  the `fdatasync` of its previous write (measured: 0 of 954,493 WAL writes went into a page under
  writeback, beside a tight `sync_file_range` loop). After a restart it can: `ReadAll` in write
  mode zeroes the tail (`fileutil.ZeroToEnd`, truncate + fallocate) without a sync, and the first
  Save's flush rewrites that dirty page; with another process starting writeback, 6.5 % of the
  WAL's writes (about a third of the reopens) went into a page under writeback. None of 13,779
  logged reopens left a mixed page on disk (the overlap of a small copy with the device's read is
  narrow); a mix would read as a mid-sector cut (above). etcd-io/etcd#22709 (open) proposes the
  sync after `ZeroToEnd`, which removes this.

Written up as `nonissues/etcd-wal-torn-tail-mid-sector.md` (a test with a constructed image that
fails at upstream `main`; no captured image, so not `issues/`). `--unsafe-no-fsync` (B on every
Save) is out of scope: documented unsafe.

## The code (upstream main 6974f522338b)

The fork's checkout in `.lake/go-src/etcd` (ce3dbc097, `goose-lean`) has the same `decoder.go`,
`encoder.go`, `pagewriter.go`, `fileutil.go` (`ZeroToEnd`), `Save`/`sync` and repair path in
bootstrap; its `ReadAll` differs only in which entries it returns.

- `Save` (`wal.go`) encodes the entries and the HardState into the encoder; only if
  `raft.MustSync` (entries, or a new term/vote) it calls `sync`: `encoder.flush` (one `write(2)` of
  the buffered bytes, a partial tail page included) then `fdatasync`, all under `w.mu`. A Save that
  does not sync writes nothing (its records stay in the buffer), except when the buffer passes
  128 KiB: `PageWriter.Write` then writes up to a page boundary and whole pages, never a page it
  wrote before. So a page is rewritten only by the flush after the `fdatasync` of its previous
  write, which waits for all writeback of the range (`file_write_and_wait_range`): no write of the
  WAL meets its own page under writeback. `cut` truncates, syncs, writes a new segment and syncs.
- `ReadAll` in write mode (`wal.go` ~552-574), after an `io.EOF`, seeks to the last valid offset
  and calls `ZeroToEnd`, not synced; bootstrap's next WAL write is the first Save's flush into that
  page.
- `decoder.go` `decodeRecord`: a zero length is the end; a frame longer than the file is
  `io.ErrUnexpectedEOF`; a record that fails to unmarshal or its CRC is `io.ErrUnexpectedEOF` only
  if `isTornEntry` (one of its sector chunks all zero, and this is the last file), else the error.
  `ReadAll` (write mode) fails on anything but `io.EOF`; `openWALFromSnapshot` calls `Repair` on
  `io.ErrUnexpectedEOF` once, and `Fatal`s on anything else.

## Setup

- `walw/` (Go module: etcd server/api/pkg/client at 6974f522338b, raft v3.7.0; go1.27.3):
  - `walw run DIR SECS SEED MINB MAXB [DMNAME]`: `wal.Create`, then `Save(hs, ents)` in a loop as
    etcd's raft loop calls it: 3 Saves in 4 carry 1-8 entries (MINB..MAXB data bytes in all,
    nonzero data determined by the index), 1 in 4 only a new Commit (not synced); one segment
    (`SegmentSizeBytes` 256 MiB, the run stops before it fills: no cut). After each synced Save a
    dm-log-writes mark `s<SEED>:<index>` through the device-mapper ioctl, so each crash point
    knows the entries acknowledged durable. `RESTART=N`: every N synced Saves, `Close`, `Open` +
    `ReadAll` (bootstrap's reopen); `RGAP=US`: a random wait up to US us after it.
  - `walw sync SECS DIR...`: another process: `sync_file_range(WRITE)` of every segment in a
    tight loop (as e2e's `tearw sync`).
  - `walw check DIR SYNCED`: etcd's bootstrap of the WAL: `Open`, `ReadAll`, `Repair` on
    `io.ErrUnexpectedEOF` (once), again; prints clean / repaired / FAIL, and LOSS if an entry up to
    SYNCED is missing, BAD if an entry's data is wrong.
  - `walw tornsim DIR NSAVES MINB MAXB SEED`: writes a WAL so (on tmpfs), records every synced
    flush `[a, b)` (the tail fd's offset from `/proc/self/fdinfo`), and for every cut
    `c = a + 4096m < b` with `a` mid-page (the buffer's page boundaries) checks the image of a cut
    there whose earlier pages landed: the file's bytes up to `c`, zeros after.
- `run.sh WORKDIR SECS [ROUNDS] [NW] [NSYNC] [MINB] [MAXB]`: as `../e2e/e2e.sh`: a C filesystem
  (8 GiB image), empty, as the base; dm-log-writes over its loop device; `c_mount`, `c_check`; NW
  writers in `w0..`, NSYNC syncers, the compaction loop (`COMPACT=1`), `wal.bt`; then the final WAL
  files (synced by `Close`) and their extents (`debugfs ex`), and `scan.py`. `NOLOG=1`: no log, for
  long page-cache counts.
- `scan.py`: every logged write is a crash point (as `../e2e/scan.py`). Each write of a WAL block
  is classified against the page's final content F: `ok` (F's first k bytes then zeros, k a sync
  point or 4096), `cut-record`, `cut-mid` (a tear inside a record; MIXED-SECTOR if not at a
  sector boundary), `mixed` (another shape). Images (built from base + log, recovered by a kernel
  mount, mounted read-write, `walw check` on every WAL with its last mark): every odd point (up to
  `MAXIMG`) and `NSAMPLE` (40) points spread over the log. `ATTR=content` attributes blocks by
  content (a reopen's truncate + fallocate moves the blocks after the tail).
- `wal.bt`: `../e2e/tear.bt` for `walw` (tears in the page cache: `ext4_da_write_end` with
  `0 < copied < len` ending mid-page; writebacks of the torn folio while torn, `WB-TORN`).
  `wb.bt COMM`: writes (`ext4_da_write_end`) into a folio under writeback (`PG_writeback`).
  `wbcount.sh WORKDIR SECS tearw|walw [NW]`: wb.bt on a C filesystem, no log.

## Results (`results/`)

| run | config (8 writers, 1 syncer, compaction loop, C) | Saves (synced) | reopens | page writes logged: classes | images / WAL checks |
|---|---|---|---|---|---|
| `C1` | 40 s, 50..6000 bytes a Save | 566,466 (425,803) | 0 | 759,367: all ok | 40 / 320: 163 clean, 157 repaired |
| `R1` | 20 s, `RESTART=200` | 135,418 (101,763) | 508 | 182,797: all ok | 40 / 320: 253 clean, 67 repaired |
| `R2` | 30 s, `RESTART=5 RGAP=100`, 50..400 | 46,636 (34,935) | 6,987 | 54,050 (block map): 54,048 ok, 2 mixed | 42 / 336: 322 clean, 14 repaired (both mixed points' images: clean) |
| `R3` | as R2, `ATTR=content` | 47,779 (35,790) | 7,158 | 55,286: all ok | 40 / 320: 301 clean, 19 repaired |
| `R4` | 30 s, `RESTART=3 RGAP=100`, 2000..4000, `ATTR=content` | 26,543 (19,865) | 6,621 | 52,915: all ok | 40 / 320: 282 clean, 38 repaired |
| `N1` | `NOLOG=1`, 16 writers, 2 syncers, 10 x 30 s | 6,153,702 (4,621,577) | 0 | - | - |

No FAIL, LOSS or BAD in any check. "repaired": the crash cut a Save whose record spans an
unwritten (zero) sector: `io.ErrUnexpectedEOF`, `Repair`, the synced entries all there.

R2's two `mixed` points were classified by the final block map, which reopens invalidate (the
blocks after the tail are freed and reallocated); their images were clean and the log was not kept,
so they are most likely blocks attributed to the wrong page; R3 and R4 (by content) found none.

Page cache (`wal.bt`): one tear (cut at in-page 24, window 16-32 us) in R1, none in C1, R2-R4 or
N1 (8.5 M `write_end` calls in N1; the counts of concurrent runs overlap: `comm` is `walw` for all);
no writeback of a torn folio (`WB-TORN` 0) anywhere. The e2e's `tearw` saw 1-2 tears per 3·10^7
writes with buffers filled just before the write, as the `PageWriter`'s are.

Writes into a folio under writeback (`W1`, `wbcount.sh`, 30 s, 8 writers): `tearw` (control, 10 s,
4 writers): 3,257,448 of 11,401,220; `walw` steady (50..6000): 0 of 954,493; `walw RESTART=5`
(50..400, ~7,475 reopens each): 2,800 of 42,511 (`RGAP=100`) and 2,755 of 43,184 (`RGAP=0`).

`tornsim` (`T1`): Saves of 50..6000 bytes: 812 cuts at the buffer's page boundaries, 194 FAIL (CRC
mismatch or protobuf error), 597+12 repaired, 9 clean; 4100..8000 bytes: 467 cuts, 78 FAIL. A FAIL
is a cut whose record ends in the cut's sector (no later all-zero sector), e.g. flush
`[33512, 37848)`, cut 37608 (in-page 744): `walpb: crc mismatch ... at position: 37208`.

## Why nothing failed end to end

A needs three things at once: compaction migrating the second page of the `PageWriter`'s buffer
during the copy (rare: the buffer is written just before), a writeback of the WAL page in the torn
window (only another agent: the Save's own `fdatasync` starts after the copy), and a crash before
the Save's `fdatasync` completes. B needs a reopen (steady state is immune), a writeback in flight
over the first Save's copy, the device reading the page during that copy (tens of ns for a small
Save), and the crash in the same window. In production, the "other agent" is the kernel flusher
under dirty-memory pressure or a `sync`/`syncfs` by another process; both are rarer than the tight
loop here. So: possible, and fatal to the member when it happens (a manual WAL repair or a re-add);
not reproduced.

## Reproduce

Root via sudo, dm-log-writes, bpftrace with BTF, go1.27.3. WORKDIR with room for the log (1.5-8 GB
a run; here `/tmp`, tmpfs):

```
H=notes/axiom-review/fs-v2-r6/wal
$H/run.sh /tmp/walx/r1 40 1 8 1                                             # C1
RESTART=200 $H/run.sh /tmp/walx/r2 20 1 8 1                                 # R1
RESTART=5 RGAP=100 $H/run.sh /tmp/walx/r4 30 1 8 1 50 400                   # R2
ATTR=content RESTART=5 RGAP=100 $H/run.sh /tmp/walx/r5 30 1 8 1 50 400      # R3
ATTR=content RESTART=3 RGAP=100 $H/run.sh /tmp/walx/r6 30 1 8 1 2000 4000   # R4
NOLOG=1 IMG=16G $H/run.sh /tmp/walx/r3 30 10 16 2                           # N1
$H/wbcount.sh /tmp/walx/wb 10 tearw 4; $H/wbcount.sh /tmp/walx/wb 30 walw 8  # W1
RESTART=5 RGAP=100 MINB=50 MAXB=400 $H/wbcount.sh /tmp/walx/wb 30 walw 8
(cd $H/walw && go build -o /tmp/walx/walw .) && /tmp/walx/walw tornsim /tmp/walx/ts 3000 50 6000 1   # T1
```

Some runs overlapped (R1 with C1's scan, R2 with N1), which changes rates, not classes. No loop or
dm device was left after the runs.
