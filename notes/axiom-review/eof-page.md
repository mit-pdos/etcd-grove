# The page holding EOF, past the size (2026-11-13, branch `wal-eof`)

**Question** (the WAL proof, `notes/wal-fsext-plan.md`, W6 third session, task 1 point 3): the
file extension (`GooseLang/Ext/Fs/Impl.lean`) keeps whatever the page holding a file's end holds
past its size (`OsFile.ofDisk`, "stale ones included"); a later write over those bytes has their
old values among its crash candidates, so a power loss could bring stale bytes back under the
size, inside the WAL's records. Is that Linux, or is the model loose? And the WAL reaches it: a
`Save` crossing `SegmentSizeBytes` leaves the tail at an unaligned size, `ReadAll`'s `ZeroToEnd`
(`ftruncate(off)`, then `fallocate(0, 0, lenf)`; the fork adds an `Fdatasync` after it) keeps an
unaligned size, and the next `Save` writes past it.

**Answer.**

1. **Linux does allow stale bytes under the size after a power loss**: a crash can leave data of
   an append on disk past the recovered size (`fs-v2-f3/f3.sh`), and a later append into that
   block, with no truncate first, can be made durable as a size covering the stale bytes without
   its data (`pl-append` below: size 5010 reading the stale `53`s). The model allows exactly that.
2. **But not on the WAL's path**, and there the model is **sound but loose**: every `ftruncate`
   (shrinking, to the same size, or growing) zeroes the rest of the block holding EOF, in the page
   cache and, ordered before the truncate's transaction, on disk (`trunc-*`, `zerotoend`,
   `pl-trunc-append` below). The model's `ftruncate` announces zeros only between the old and new
   sizes (`OsChange.ofResize`), so after `ZeroToEnd` and its `Fdatasync` the model keeps the stale
   bytes past `lenf` as their one candidate, where Linux has zeros. Proposed change P2 below.
3. **A soundness gap found on the way** (not the WAL's question, the other direction): writeback
   of the page holding EOF zeroes it past the size, in the page cache and on disk
   (`ext4_bio_write_folio`). A sync (`OsFile.synced`) keeps the stale value as the byte's one
   candidate, and between syncs no change announces zero there, so the model **excludes** a real
   outcome: `pl-wb-zero` and `pl-wb-zero-bg` below recover size 5020 reading `00` at bytes
   5010..5019, where the model allows only the stale `53` or the written `43`. Proposed change P1.

Neither is implemented: both are trusted changes for the user's review [user], P1 changes
`CrashFile` (every crash proof that reads a byte's candidates: `FileCrashedR` and its clients,
the WAL's files among them, under concurrent work), and P2 changes the resize machinery shared
by `ftruncate` and `fallocate` (`wp_osResizeStart`, `rsTok`/`rsDone`/`rsUndone`, a kind for
`fallocate`). Drafts below.

## What ext4 does (Linux v7.0, configuration C: 4 KiB pages = blocks, `data=ordered`, delalloc)

Source: v7.0 from kernel.org (`eof-page/fetch-src.sh v7.0 DIR`); line numbers at v7.0.

- **Truncate, shrinking or to the same size.** `ext4_setattr` (`fs/ext4/inode.c:5794`) calls
  `truncate_pagecache(inode, i_size)` (`:5995`), which zeroes the partial folio from the new size
  to its end and drops the folios past it (`mm/truncate.c:779`, `truncate_inode_partial_folio`
  `:217-246`), then `ext4_truncate` "even if i_size didn't change" when `ia_size <= oldsize`
  (`:5996-6003`). `ext4_truncate` zeroes the block holding the (unaligned) size to its end:
  `ext4_block_truncate_page(handle, mapping, inode->i_size)` (`:4556-4557`), whose comment says
  why: "We need to physically zero the tail end of that block so it doesn't yield old data if the
  file is later grown" (`:4140-4143`). `__ext4_block_zero_page_range` (`:4015-4109`) zeroes the
  folio range, marks the buffer dirty and, for a written block in ordered mode, adds the range to
  the transaction's ordered data (`ext4_jbd2_inode_add_write`, `:4096-4102`): the commit that
  carries the truncate waits for the zeroed block. Blocks past the new size's block are freed.
- **Truncate, growing.** `ext4_setattr`: "tail zero the EOF folio on truncate up":
  `ext4_block_truncate_page(handle, mapping, oldsize)` when `oldsize` is unaligned (`:5943-5948`),
  in the handle that sets `i_disksize` (`:5958-5975`).
- **fallocate(0) growing.** `ext4_alloc_file_blocks` (`fs/ext4/extents.c:4649-4658`), per chunk:
  the size to `epos` and `ext4_zero_partial_blocks(handle, inode, old_size, epos - old_size)`:
  from the old size to the end of its block if `epos` is past that block, **only to `epos`
  otherwise** (`ext4_zero_partial_blocks`, `inode.c:4162-4198`: one partial range within a block).
  A non-growing `fallocate(0)` (`new_size = 0`, `extents.c:4816-4822`) and `FALLOC_FL_KEEP_SIZE`
  zero nothing.
- **A write past the size.** `ext4_da_do_write_end` (`inode.c:3202-3268`): for `pos > old_size`,
  `ext4_zero_partial_blocks(handle, inode, old_size, pos - old_size)` (the gap, ordered). A write
  starting at or below the size zeroes nothing; if its end is inside an allocated block,
  `i_disksize` is updated at once (`ext4_da_should_update_i_disksize`, `:3244-3247`), not ordered
  with the data: the stale exposure of point 1.
- **Writeback.** `ext4_bio_write_folio` (`fs/ext4/page-io.c:458`): "The folio straddles i_size.
  It must be zeroed out on each and every writepage invocation", `folio_zero_segment(folio, len,
  folio_size(folio))` (`:476-483`): the page cache's folio itself is zeroed past the size, and the
  block written with those zeros. A clean folio is not written: a stale tail read from disk stays.
- **Reads.** `ext4_mpage_readpages` reads the block holding EOF whole (`fs/ext4/readpage.c:254-257`,
  `last_block_in_file` rounds the size up to a block): a stale tail on disk is in the page cache
  (visible through a mapping, `none` below), never through `read(2)`.
- `pagecache_isize_extended` returns at once with 4 KiB blocks (`mm/truncate.c:850`, `bsize >=
  PAGE_SIZE`): on C the zeroing is ext4's own (the calls above).

## Measured on C (`eof-page/eof.sh WORKDIR SCENARIO`, results in `eof-page/results/`)

Every scenario starts from a synced file of size `SZ` (5000; 9000 for `zerotoend`) whose block
holding EOF holds `41` below the size and the stale `53` past it on disk (planted: written to the
block's end, synced, unmounted, `debugfs -w sif /f size SZ`; the state `fs-v2-f3/f3.sh` reaches
by a crash). The page cache past the size is read through a mapping (`eof-page/mread.py`); "disk"
is the raw block after the sync and an unmount.

| scenario | page cache past the new size | disk after fsync |
|---|---|---|
| `none` (fsync only) | `53` | `53` (a clean folio is not written) |
| `trunc-eq` (`ftruncate(5000)`) | `00` | `00` to the block's end |
| `trunc-down` (`ftruncate(4500)`) | `00` | `00` from 4500 |
| `trunc-up-in` (`ftruncate(6000)`) | `00` | `00` from 5000 |
| `trunc-up-past` (`ftruncate(9192)`) | `00` | `00` from 5000 |
| `falloc-in` (`fallocate(0, 0, 6000)`) | 5000..5999 `00`, **6000.. `53`** | `00` from 5000 (writeback of the dirty folio) |
| `falloc-past` (`fallocate(0, 0, 9192)`) | `00` | `00` from 5000; block 2 unwritten |
| `falloc-keep` (`KEEP_SIZE`, 5000, 4096) | `53` | `53` |
| `write-append` (`42`×10 at 5000) | 5010.. **`53`** | 5010.. `00` (writeback) |
| `write-gap` (`42`×10 at 6000) | 5000..5999 `00` | gap `00`, past 6010 `00` |
| `zerotoend` (9000: `ftruncate(100)`, `fallocate(0,0,9000)`, `fdatasync`) | `00` | block 2 unwritten (reads `00`) |

Power loss (`crash.sh`'s method: the journal's blocks linear, every other block behind `dm-delay`
20 s; `commit=1`; periodic writeback off; the image copied 4 s after the change and again 26 s
after, then recovered by a kernel mount):

| scenario | image at 4 s | image at 26 s |
|---|---|---|
| `pl-append` (`42`×10 at 5000) | size 5010 reading **`53`×10** (stale under the size) | the same |
| `pl-trunc-append` (`ftruncate(5000)`, then `42`×10 at 5000) | size 5000 (the commit waits for the ordered zeroing) | size 5010, `42`×10, `00` past |
| `pl-wb-zero` (`42`×10 at 5000, fsync, `43`×10 at 5010) | size 5020, 5010..5019 **`00`** | the same |
| `pl-wb-zero-bg` (the same, `sync_file_range(WRITE)` for the fsync) | size 5020 reading `53` (allowed) | size 5020 reading `42`, `43`; `00` past 5020 (allowed) |

(`pl-wb-zero-bg` did not show the zero: the second write reached disk with the first writeback.
The zero needs the second write's size committed after the first writeback and before its data,
which `pl-wb-zero`'s fsync arranges.)

`pl-wb-zero` in the model: after the crash-left state (`ofDisk`, bytes 5010.. of candidates
`[(53, 0)]`), the write of `42` and the fsync (`synced`: their one candidate is the page cache's
`53`), the write of `43` (candidates `[(53, 0), (43, n)]`): a crash of size 5020 has 5010..5019
each `53` or `43`. Linux gives `00`: the model excludes a real outcome.

## Verdict

- **Sound but loose** for the WAL's question: Linux zeroes the tail at every `ftruncate`; the model
  keeps the stale candidate. Nothing to record in `issues/`/`nonissues/`: the WAL never appends
  into a tail it has not truncated in the same boot (`ReadAll` in write mode always runs
  `ZeroToEnd`, `wal.go:604-621`), so the real stale exposure (`pl-append`) is not its path.
- **Unsound** in the other direction (P1): the writeback zeroing.

## Proposals [user]

### P1 (soundness): a byte past the smallest size since the last sync may come back zero

`CrashFile` (`Impl.lean`):

```lean
    (∀ b, (∃ s, (img b, s) ∈ f.cand b) ∨ (f.sizeLo ≤ b ∧ img b = 0)) ∧ f' = OsFile.ofDisk img sz
```

with the header's "Durable zeros" gaining: "Writeback zeroes the page holding the end past the
size (`ext4_bio_write_folio`): a byte that was past the size at some writeback since the last
sync, so at or past `sizeLo`, may come back zero whatever its candidates." Why `sizeLo`: writeback
zeroes past the size of the moment, at least `sizeLo` (a shrink in flight announces zeros past its
target anyway); a byte below `sizeLo` was below the size since the last sync and is never zeroed.
After a sync `sizeLo` is the size, so the sync's stale candidate is covered too, and no dirty bit
is needed. Adding an outcome is sound; it loosens only unsynced bytes (at or past the last synced
size), where every client already sees torn writes.

Ripple: `Bridge.crash_byte`/`crash_keeps` (a disjunct), `FileCrashedR` (`CrashFiles.lean`: "one of
the byte's candidates, or zero at or past `m.lo`", from `OsMeta`'s `hok.lo : m.lo ≤ f.sizeLo`), its
clients (`CrashTok`, `CrashTakeFiles`, `LinuxFs/Proof/os/Crash*`, walfs, bboltfs `CrashOk`/`P1Sat`,
the WAL's `Abs`, `Crash*`, `Cut*`), `Tests.lean`. P1 (minibolt) is about meta slots below the
synced size: unaffected. `SectorWhole` (the WAL's premise, stated on `valAt`) would exclude a
zeroed sector past `sizeLo`, a real outcome; it is not used by the WAL's proof over `fsExt`
(`wal-fsext-plan.md` 2.5). Alternative to weigh: the sync and `ofDisk` record zero as a second
stamp-0 candidate of the bytes past the size in its page, which keeps `CrashFile` but breaks "the
first candidate is the value at the last sync".

Go example to add with it (`examples/osfs/semantics/data_writeback_tail_zeros.go`): the decision,
`CrashFile`/`Tests.lean` names, allowed "size 5020 reading `00` at 5010..5019", the evidence
`pl-wb-zero` and `ext4_bio_write_folio`; and `data_append_old_block.go`'s "Decision" gains "or
zero, once a writeback of the page has zeroed them".

### P2 (precision): `ftruncate` zeroes the rest of the page holding the old end

```lean
/-- A resize of `f` to `sz`, by `ftruncate` (`trunc`) or by `fallocate`'s growth, as its first step
announces it: zeros from where the old and new sizes part; `ftruncate` also zeroes the rest of the
page holding the old end (ext4 zeroes the block holding EOF to its end: `ext4_block_truncate_page`
from `ext4_truncate`, shrinking or at the same size, and from `ext4_setattr`'s growth; the pages
past it are freed or holes), `fallocate` only up to its target (`ext4_zero_partial_blocks`). -/
def OsChange.ofResize (i : Ino) (f : OsFile) (sz : Nat) (trunc : Bool) : OsChange :=
  { ino := i, kind := if trunc then .truncate sz else .falloc sz, lo := min f.size sz,
    hi := if trunc then max (pageEnd f.size) sz else max f.size sz, val := fun _ => 0,
    target := sz }
```

with `pageEnd x := 4096 * ((x + 4095) / 4096)` in `Impl.lean` (Bridge's `pageUp` becomes it), a
kind `OsChangeKind.falloc` (`FallocStart`/`FallocFinish` use `ofResize … false`; `FtruncateStart`
and `O_TRUNC` `true`). Shrinking: `[sz, pageEnd old)`; same size: `[old, pageEnd old)`; growing:
`[old, max sz (pageEnd old))`. `land` zeroes the page cache there, so a sync makes them `[(0, 0)]`.
Sound: the zero is a disk outcome (ordered with the truncate, or the block freed), the old
candidates stay (a crash before the truncate's commit), and the page cache is zero there
(`trunc-*`). A `fallocate` keeps today's range (`falloc-in`: past its target the page cache keeps
`53`; the disk's zeros there come from writeback, P1). The environment's "no allocation failure in
the write path" extends to the truncate's zeroing (`__ext4_block_zero_page_range` gets the folio
with `FGP_CREAT` under `~__GFP_FS`, and `ext4_truncate` ignores its failure: a memory-cgroup at its
limit could skip the zeroing of an uncached folio, leaving the stale tail on disk under a
successful `ftruncate`).

Ripple: `Ghost.lean` (`TokInfo.lo/hi/val/target` for `.falloc`; `.truncate`'s `hi`),
`Truncate.lean` (`ofResize_is`, `wp_osResizeStart` and the finish lemmas: the range `[min, hi)` of
`mcells`, `rsUndone`'s `announce` bounds, `osCoh_start`'s premises), `Falloc.lean`,
`TreeSharedTrunc.lean` (`O_TRUNC`: `hi` becomes `pageEnd old`), `Tests.lean` (`cacheOk_step`'s
resize cases, `fGrow`), `World.lean`, LinuxFs `CrashOk`/`CrashSt` (the kind). The `OsMeta` effect
(`announce`'s `zf := max z hi`) is generic.

Go example (`examples/osfs/semantics/data_truncate_tail_zeros.go`): `ftruncate` to the same,
a smaller or a larger size zeroes the page holding the old end past the size; evidence `trunc-*`,
`zerotoend`, `pl-trunc-append`, the source above; allowed after `ftruncate(5000)` and a sync:
`00` past 5000; excluded: `53`.

### What the WAL proof needs

With P2, after `ZeroToEnd` (`ftruncate(off)`: zeros on `[off, pageEnd lenf)`; `fallocate` to `lenf`:
zeros on `[off, lenf)`) and the fork's `Fdatasync`, every byte from `off` on has the one candidate
`(0, 0)`. The ghost (untrusted) then needs to know it: an `OsMeta` fact "the page cache is zero past
the size" set by an `ftruncate`'s landing, kept by writes (`written` zeroes the gap, the bytes past
the new end keep their zero) and by `fallocate`, and turned by a sync into `zf := some size` instead
of `pageUp size`. With P1, `FileCrashedR` gives "a candidate, or zero at or past `m.lo`": the
tail's unsynced bytes may be zero, which W1 already treats as a torn record. Without P2 the WAL's
proof cannot exclude a stale frame past `lenf` (the plan's item 3), with no premise that Linux makes
true short of the model change: no fork change is needed (the code is right on C).

## Dispositions (2026-11-13, branch `wal-p12`; the coordinator's decisions, the user away: both **pending the user's review**)

### P1: implemented as proposed (commits `fbe4414da3`, `287794cf0e`)

Trusted: `CrashFile`'s byte clause is now
`(∀ b, (∃ s, (img b, s) ∈ f.cand b) ∨ (f.sizeLo ≤ b ∧ img b = 0))`; the header's crash rule says
"or zero at or past the smallest size since the last sync", and a new paragraph "Writeback zeroes
the page holding the end past the size" (`ext4_bio_write_folio`, `pl-wb-zero`). Go example
`examples/osfs/semantics/data_writeback_tail_zeros.go` (indexed in `doc.go`;
`data_append_old_block.go` and `data_crash_candidates.go` point to it). The alternative (zero as a
second stamp-0 candidate at a sync) was not taken.

Repaired (no `sorry`, no axiom): `Bridge.crash_byte` (the disjunction), `crash_keeps` (takes
`b < f.sizeLo`); `FileCrashedR` (a run's byte: a candidate, or zero at or past `m.lo`) and
`crashSeen_crashed`; `LinuxFs/Proof/os/CrashWrite.lean` (`WriteCrash` gains the disjunct
`min m.lo (wT …) ≤ b ∧ f.cache b = 0`, `fileCrashedR_byte` returns the disjunction,
`crashed_dur` takes `b < M.lo`); crashlog (`crash_W1`: a zero flag is no flag; `crash_W2` takes
`8 ≤ m.lo`, true after its sync), walfs (`synced_good`, `dataGood_start`, `start_key`: the data
bytes are below the synced size), minibolt (`kc_cand` also gives `s.vmeta.lo ≤ f.sizeLo`;
`CrashImg.byte` gains the disjunct; `crashImg_clean`, `slotK_same`, `image_take_drop` take the
byte below `s.vmeta.lo`, which every use meets: metas and root pages are below `lo`); the WAL's
`durable_img` and `TailCrash` (the tail's bytes are below `g.om.lo = g.bs.length`).
`Tests.crash_after_sync` now concludes `f'.contents = f.contents` (past the size the last page may
come back zero); new test `crash_wb_tail_zero`. `P1Sat.p1_untouched` (minibolt's premise P1 never
fails on an untouched file) is restated for a slot below the file's synced size: past it a
writeback can tear an untouched slot, which P1 then assumes does not validate, as for any torn
slot (`BootP1.lean`'s header says so). Every module importing `Impl.lean` rebuilt (92 leaves),
except `wal/filePipeline__alloc.lean`, which failed at a step unrelated to the crash relation
("cannot frame zapLoggerOk lg", in its error branch's `zap` call; not investigated here).

### P2: implemented, with one change to the range (commits `b9bf235570`, `6523d2e15f`, `9fc1654125` checkpoints, `7b096fa72a` the trusted change)

Trusted: `pageEnd x := 4096 * ((x + 4095) / 4096)` (`Bridge.pageUp` replaced by it); a kind
`OsChangeKind.falloc`; `OsChange.ofResize i f sz (trunc : Bool)` with
`hi := if trunc then pageEnd (max f.size sz) else max f.size sz` (`FtruncateStart` and `O_TRUNC`
`true`, `FallocStart` `false`, `FallocFinish` on `.falloc`); the header's "An `ftruncate` zeroes the
rest of the page holding the old end" and "no allocation failure in the write path" widened to the
truncate's zeroing. Go example `examples/osfs/semantics/data_truncate_tail_zeros.go`.

**The change from the draft**: `pageEnd (max old sz)`, not `max (pageEnd old) sz`. They differ only
for a growth into a later page, where the new range also covers the new last page past the new size
(a hole: zeros, `trunc-up-past` measured `00` there), so it is as sound. Why: with the draft a
second resize to the size the file already has (`os.File.Truncate`'s `EINTR` retry, the crash
state's loop) announces bytes the first did not, and `rsPost_rsPost` (repeating a resize changes
nothing) fails; with `pageEnd (max …)` it holds, and the retry's landed state stays a function.

Repaired (no `sorry`): `Truncate.lean` (`rsKind`/`rsHi`, `tr : Bool` on `rsTok`/`rsDone`/`rsUndone`/
`rsPost`), `Falloc.lean`, `TreeSharedTrunc.lean`, `Tests.lean` (new `trunc_same_synced_zero`:
after `ftruncate` to the same size and a sync, bytes 5000..8191 have the one candidate `(0, 0)`),
LinuxFs's `os`/`syscall`/`unix` resize specs, fileutil, minibolt, walfs `SegLog`, the WAL's
`Inv`/`CrashTakeSeg`. **Client obligation changed**: the mapped cells of a resize spec are
`[min size tg, rsHi tr size tg)` (the flag of a mapped cell past the end flips while the change is in
flight), `O_TRUNC`'s open `[0, pageEnd size)`; clients without mappings are unaffected, minibolt
converts its one mapping (`mcells(Any)_single_past`).

**Not done: the WAL's fact** ("the page cache is zero past the size", making a sync give
`zf := some size`). The ghost records nothing of the page cache past the size, so it needs a new
`OsMeta` field (an interval known zero in the page cache: set by an `ftruncate`'s landing to
`[tg, pageEnd (max s tg))`, kept by `fallocate`, shrunk by writes; a sync whose size lies in it gives
`zf := some size`) and its upkeep in `MetaOk` wherever it is re-established (start, landing, sync,
crash). Next unit; with it `ZeroToEnd` (whose `ftruncate` from `lenf` zeroes `[off, pageEnd lenf)`)
followed by `Fdatasync` gives the WAL every byte from `off` on durable zero.
