# fs-v2-r6 e2e: a torn page on disk from one aligned 4096-byte pwrite, on configuration C

**Date:** 2026-11-11. **Result: caught.** On configuration C (`../../fs-config/README.md`: Linux
7.0.0-38-generic, ext4 made by `mkfs-mount.sh` with its defaults, default mount, every filesystem
passing `check.sh`), a Go program (go1.27.3) that overwrites page 0 of a file with one
`os.File.WriteAt` of 4096 bytes at offset 0, from a heap buffer at `addr % 4096 = 0xd10`
(minibolt's commit buffers' offset, round 6 A1), leaves crash images in which that page is
**bytes 0-751 the new value, 752-4095 the old one** (sector 1 holds two values), after kernel-mount
recovery; an application boot that checks its records panics on them. No fault injection in the
program (no `userfaultfd`, `mprotect`, `munmap`, signals); the environment is: memory compaction
(a loop writing `/proc/sys/vm/compact_memory`, as `../tear/run.sh`) and another process starting
writeback of the file in a tight loop (`sync_file_range(SYNC_FILE_RANGE_WRITE)`).

Rate: 7 to 14 such images in every run of 40-120 s with 8 writers (5 runs, 49 images in total), each
matching one writeback that bpftrace saw take the folio inside its torn window. Separately, and
much more often, a second mechanism tears pages on C with **aligned** buffers and **no**
compaction (B below): 1.3-2.2 % of the page's writebacks.

## What tears, and why it reaches the disk

**A: the source page boundary (the mechanism of round 6's A1).** The buffer crosses a page
boundary 752 bytes in. `generic_perform_write` copies with page faults disabled; when compaction
has replaced the second source page's PTE by a migration entry, the copy stops at byte 752,
`ext4_da_write_end` commits the 752-byte prefix of the uptodate folio and unlocks it, and the loop
retries (`mm/filemap.c` v7.0, lines 4313-4381): `write_begin`, a copy that faults again (copied 0),
`write_end`, then `fault_in_iov_iter_readable`, which sleeps until the migration ends. Through that
window the folio is unlocked and dirty, bytes 0-751 new and 752-4095 old. tear.bt measured the
window at 1 us to 512 us (mostly 16-512 us). A writeback that locks the folio in the window
(`ext4_bio_write_folio`) writes it torn; a crash after that write and before the rest is written
back leaves the torn page on disk.

**B: no stable pages (the "no mixed writeback" assumption).** `NoTear.lean`'s header says
"Writeback locks the folio and so cannot start in the middle of its copy (the no-mixed-writeback
assumption: the device writes the sectors as they are when writeback took the page)". ext4 unlocks
the folio once it is marked under writeback, before the device reads its data, and on a device
without `stable_writes` (C's: `/sys/block/vda/queue/stable_writes` is 0 on this machine, as on a
plain NVMe/virtio disk; the loop and dm devices here are 0 too) `write_begin` does not wait for
writeback (`folio_wait_stable` waits only for a stable-writes mapping). So the next `pwrite` copies
into the folio while the device's copy of it is in progress, and the device gets a mix of two
consecutive writes, at any byte (cuts at 8, 64, 192, ..., several runs). This needs neither a
misaligned buffer nor compaction, only a `pwrite` of a page whose previous write is being written
back (a page rewritten before it was synced). It also tears sector 0.

`STABLE=1` sets the dm device's `stable_writes` before the mount (ext4 then marks the mapping
stable and `write_begin` waits for writeback): this removes B and isolates A. It is a property of
the device, not of a mount or `mkfs` option, but it is not C's device (C's do not require stable
writes), so A is also shown on C exactly (`STABLE=0`), told apart from B by its signature (one cut,
at 752, new prefix) and by bpftrace's count of writebacks inside a torn window.

## Setup

- `tearw.go` (go1.27.3): `tearw init DIR N` makes `f0..f{N-1}`, one page of zeros each, fsynced;
  `tearw write FILE SKEW SECS POOLMIB [once|each]` overwrites page 0 of FILE, 4096 bytes at
  offset 0 per `WriteAt`, never syncing, with a page of one byte value (consecutive writes,
  consecutive values in 1..255), from slot k of a 256 MiB heap pool, slot k = the 4096 bytes at
  `k*4096 + SKEW` (k = 0, 2, 4, ...), filled once before the loop (records prepared in memory
  before they are written; `each`: filled just before each write, below); `tearw sync DIR N SECS`
  is the other process: `sync_file_range(fd, 0, 4096, SYNC_FILE_RANGE_WRITE)` on every file in a
  tight loop (starts writeback of a dirty page 0, does not wait).
- `boot.go`: the application's boot. It reads page 0 of each file through the recovered filesystem
  and panics unless every 512-byte sector is one byte value: the weakest thing the Fs v2 crash rule
  promises (each sector a version it had, `NoTearCrash`'s page cuts), a stand-in for a record
  checksummed within a sector. A page whose sectors hold different values is reported, not a
  panic (the semantics allows it).
- `tear.bt`: per tearw inode, a tear (`ext4_da_write_end` with `0 < copied < len` ending inside the
  page), its window (until the next `write_end` with `copied > 0`), and writebacks
  (`ext4_bio_write_folio`) of the folio while it is torn (`@wb_torn`, `WB-TORN` lines).
  `mig.bt` (diagnostic): migrations of the writers' pages (`try_to_migrate_one` on their mm).
- `e2e.sh WORKDIR SKEW SECS [ROUNDS] [NW] [NSYNC]`: per round, `c_mkfs`, `c_mount`, `tearw init`,
  `sync`, unmount, a copy as the base image; then `dm-log-writes` over the loop device (log on a
  20 GiB sparse file), `c_mount` of the dm device, `c_check` (must pass), tear.bt, the compaction
  loop, NSYNC syncers and NW writers for SECS seconds; unmount; `scan.py`.
- `scan.py`: every write in the log is a crash point (dm-log-writes logs writes in completion
  order; the base plus the log's writes up to and including one is a state a crash of a
  flush-honouring device can leave). Each write of a file's page-0 block is checked (torn: more than
  one byte value; mixed sector: a run boundary not a multiple of 512). For the first MAXIMG torn
  points (source-boundary cuts first) it builds the image, recovers it exactly as `c_recover` does
  (`mount -t ext4`, which replays the journal, then `umount`), mounts it read-only, reads each
  file's page 0 through ext4 and runs `boot`.
- What the log holds: dm-log-writes copies each write bio's data when it maps the bio (in the
  submitter's context, after ext4 has marked the folio under writeback). With stable writes
  (`STABLE=1`) the folio cannot change until the write completes, so that copy is what any device
  reads. Without, it is one read of the page during the I/O, as a device's DMA is one.

## Results

`results/*.txt` are the runs' outputs (the `TORN` lines cut to the source-boundary ones and the
first 20 others). "writes" are `ext4_da_write_end` calls (a torn write makes 2-3).

| run | config | writes | tears in the page cache (cut 752) | writebacks in a torn window | page-0 writebacks logged | torn on disk: A (cut 752, new prefix) | torn on disk: other (B) | booted images |
|---|---|---|---|---|---|---|---|---|
| `S2` | skew 0xd10, STABLE=1, compaction, 8 writers, 1 syncer, 120 s | 158.3 M | 15 | 7 | 2,409,254 | **7** | 0 | 3: all panic (`torn sector 1`) |
| `C1` | the same, STABLE=0 (C exactly) | 268.6 M | 37 | 14 | 3,394,522 | **14** | 50,764 (50,179 with a mixed sector) | 3 A images: all panic |
| `C2` | C exactly, 3 rounds x 40 s | 3 x ~114 M | 37 / 30 / 19 | 11 / 8 / 9 | 1.22 M / 1.24 M / 1.22 M | **11 / 7 / 10** | 16,330 / 16,213 / 15,311 | 1 A image per round: all panic |
| `B1` | skew 0 (aligned), **no compaction**, STABLE=0, 30 s | 70.3 M | 0 | 0 | 749,451 | 0 | **16,707** (15,833 with a mixed sector) | 2: both panic (`torn sector 0`, `torn sector 1`) |
| `S0` | skew 0, STABLE=1, compaction, 120 s (control for A) | 147.9 M | 0 (24 copies faulted at byte 0) | 0 | 2,325,725 | 0 | 0 | - |
| `A3` | skew 0xd10, compaction, no syncer, 4 writers, 30 s (page-cache rate only) | 31.7 M | 10 | - | - | - | - | - |

A typical A image (`S2`, after log write 10564): f3's page 0 reads `0xce` in bytes 0-751 and
`0xcd` in 752-4095 after recovery; `boot` prints the other files' records and
`panic: .../f3: torn sector 1: byte 512 = 0xce, byte 752 = 0xcd`. In `S2` every on-disk A tear is
one of the 7 writebacks bpftrace saw inside a torn window, and nothing else is torn. On C exactly
(`C1`, `C2`) the A counts are within one of `@wb_torn` (B can disturb a caught A page, or produce a
752 cut by chance: `C1` has one old-prefix 752 cut).

**When.** Most A tears come in the first one or two seconds of a run: in `C2` 25 of the 28 A images
are among the first 44,000 of ~1.2 M log writes (the log takes ~30,000 writes a second), a few later
(log writes 384,603 to 992,980). The writers' pools are freshly allocated; compaction migrates them
first (`mig.bt`, 30 s of `A3`'s setup: 177,874 of the 286,633 migrations were of the writers' pages)
and they then settle in the zone's upper part.

**What makes A frequent.** Filling each slot just before its write (`FILL=each`) gave 1-2 tears in
the page cache per 30 s (4 writers, 30-34 M writes; not run to disk), against 10 with `FILL=once`
(`A3`). A plausible reason is that a slot touched just before the copy is rarely mid-migration
when the copy reaches it; not established (`mig.bt` counted the same 43-44 `migration_entry_wait`s
of the writers per 30 s in both). Another process's memory churn (`CHURN=8192`, 8 GiB released and
re-touched a page in two, with `FILL=each`) raised the machine's migrations a hundredfold (the compaction
loop alone: 2,500/s; with the churn: 218,000/s; measured without writers) but gave 0 tears in 30 s. Not measured: A without the compaction loop (only
kcompactd, `vm.compaction_proactiveness = 20`, and direct compaction): the loop was not left out in
any run that caught a tear on disk.

## What this shows of the Fs v2 semantics

- A (source page boundary): an image `NoTearCrash` excludes. The write in flight is the one whose
  prefix landed; sector 1 holds bytes 512-751 of it and 752-1023 of the previous write, neither a
  version the sector had nor the sector with a page cut of the write landed. This is round 6's A1
  observed end to end on disk, under the program assumption's failure (a buffer not at the file
  offset's page offset), as `NoTear.lean` predicts for such buffers; the machine assumption (ii)
  held (`S0`: aligned buffers, 0 mid-page tears in 1.5·10⁸ writes).
- B (no stable pages): `NoTear.lean`'s "Writeback locks the folio and so cannot start in the
  middle of its copy" does not give "the device writes the sectors as they are when writeback took
  the page": on C the folio is unlocked under writeback and rewritten while the device reads it.
  The images have mixed sectors (sector 0 included) with page-aligned buffers and no compaction.
  `fs-v2.md` already records "No mixed writeback" as an accepted assumption that "ordinary hardware
  does not justify"; this measures it false on C for a program that rewrites a page before it is
  synced. Whether a client of the semantics (minibolt, walfs) ever rewrites a page while its
  previous write may be under writeback was not checked here.

## Reproduce

Root via sudo, `dm-log-writes`, bpftrace with BTF, go1.27.3 (`GOTOOLCHAIN`). WORKDIR on a
filesystem with room for the log (5-15 GB a run; `/tmp` is tmpfs here):

```
H=notes/axiom-review/fs-v2-r6/e2e
STABLE=1 $H/e2e.sh /tmp/e2e 3344 120 1 8 1            # S2: A alone
$H/e2e.sh /tmp/e2e 3344 120 1 8 1                     # C1: C exactly
MAXIMG=1 $H/e2e.sh /tmp/e2e 3344 40 3 8 1             # C2
COMPACT=0 MAXIMG=2 $H/e2e.sh /tmp/e2e 0 30 1 8 1      # B1: B alone
STABLE=1 MAXIMG=2 $H/e2e.sh /tmp/e2e 0 120 1 8 1      # S0: aligned control
MAXIMG=0 $H/e2e.sh /tmp/e2e 3344 30 1 4 0             # A3: page-cache rate, no writeback
```

Env: `COMPACT` (1), `STABLE` (0), `MAXIMG` (3), `POOL` (256 MiB), `FILL` (`once`), `CHURN` (0 MiB);
`KEEP=1` keeps the crash images (`WORKDIR/crash.<write>.img`). The script removes its dm and loop
devices at the end of each round (none were left after these runs).
