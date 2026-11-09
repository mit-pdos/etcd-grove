# Review, round 4: the trusted changes of branch `fs-v2` (Fs v2 semantics, no-tear filter, models, results)

**Date:** 2026-11-09. **Reviewed:** branch `fs-v2` at `0bb5e59324`, against the merge base
`1fbbd2504b` with `origin/lean`. In scope: the top-level statements (`bboltfs/Results.lean`'s
`bootCrashSafety` over `BootNoTear.lean`'s `BootCrashSafety`/`NoTearCtx`; `crashlog/Results.lean`,
`walfs/Results.lean`, `walfs/SegLogResults.lean`, `walfs/DirSwapResults.lean`); the semantics
(`GooseLang/Ext/Fs/{Impl,Tree,Paths,Lookup}.lean`); the execution filters (`FilteredSem.lean`,
`AdequacyS.lean`, `NoTear.lean`); the hand-written models (`TrustedCode/os.lean`, `syscall.lean`,
`golang_org/x/sys/unix.lean`) against go1.27.3's `src/os`, `src/internal/poll` and
`golang.org/x/sys@v0.48.0/unix`; and `etc/goose.py`'s project `walfs`. Rounds 1-3
([fs-v2](fs-v2.md), [fs-v2-r2](fs-v2-r2.md), [fs-v2-r3](fs-v2-r3.md)) were read first; the
metadata half (`Tree.lean`, `Follows`, `CallBegin`) was not re-attacked except where noted.

**Method.** The `axiom` skill's, adapted to a trusted semantics, as in rounds 1-3: a finding is an
execution (a Go program, its environment, the kernel's interleaving and crash point) whose Linux
outcome the model (or a premise the theorems state) excludes, or a model rule a proof can use that
Linux does not honour. Unlike rounds 2-3, **every finding below was run** on this machine (Linux
7.0.0-38-generic, x86-64, Go 1.27.3; ext4 and xfs on loop devices, `sudo`), and the kernel claims
were read in the v7.0 source (`fs/ext4/inode.c`, `fs/jbd2/{commit,transaction}.c`, `mm/filemap.c`,
`fs/iomap/buffered-io.c`, `fs/read_write.c`, `fs/ext4/super.c`, `drivers/md/dm-delay.c`). No Lean
counterexample was built (the user's brief: report, no code changes). The scripts are reproduced at
the end and kept (untracked) in `.lake/review-r4/`.

## Verdict

**Not sound as stated: one model rule is false of ext4's default configuration, the no-tear premise
is false in three environments, and one `os` model returns a wrong count.** None of them makes a
current top-level theorem claim a false outcome, as far as checked (see each "clients" line), but
U1 refutes the decision recorded in `examples/osfs/semantics/data_ordered_growth.go` and is used by
minibolt's proof, and N1-N2 are exactly the premise `BootCrashSafety` rests on.

| # | severity | finding | evidence |
|---|---|---|---|
| U1 | **unsound** (any program; current clients: minibolt's proof uses the rule, its statement probably survives) | ordered growth (`Sector.fresh`, `CovCand`) is false on ext4 with `dioread_nolock`, the default since 5.6: a crash keeps the size that covers a new block with the block reading zeros (an unwritten extent) | **tested** (`unwritten.sh`; `dioread_lock` contrast), kernel source |
| N1 | too-strong assumption (`NoTearCrash`; minibolt's aligned buffers escape it) | a buffered `pwrite` whose source buffer meets a non-present page commits the prefix up to that page (mid-page, mid-sector) and the page can be written back before the call returns; a crash then keeps a cut that is no page cut | **tested** on ext4 (userfaultfd holds the window, `tear.c`); xfs prefaults (not reproduced), kernel source |
| N2 | too-strong assumption (`NoTearStep`, `NoTearCrash`); also origin/lean's D22 | `RLIMIT_FSIZE` not a page multiple, or ext4 with 1 KiB/2 KiB blocks near `s_maxbytes`, shortens a one-page aligned write mid-page; Go's `WriteAt` then fails with `EFBIG` having written part of the page | **tested** (Go program, `ulimit -f 6`; `mkfs.ext4 -b 1024` and `-b 2048`) |
| M1 | unsound-but-unreachable-by-current-clients | `os.File.Write`'s model returns `0` with every error; Go returns the bytes written (`poll.FD.Write`'s `nn`) | **tested** (Go program) |
| D1 | doc-only | statements and docstrings that now say false things (`data_ordered_growth.go`'s "Excluded", `NoTear.lean`'s EFAULT argument, the "Ordered growth" header, walfs's "or of the process alone") | read |
| O1 | informational (premise strength) | every result takes `Hinit_wp`, a triple about the axiomatized initializers (`axiom Stderr.init : val`, ...): consistent but unprovable on this branch; origin/lean's `os` initializer models are what would discharge it | read |

Then: what origin/lean's changes mean for fs-v2 (the merge), the attacks that failed, what was not
tried, and the scripts.

## Findings

### U1 (unsound): ext4 with `dioread_nolock` commits a covering size before the new block's data

**The model's claim.** `Sector.fresh` (`Impl.lean`, the `Sector` structure and the header's
"Ordered growth", lines 80-95): a sector whose page lay past the size at the last sync is never its
first version under a crash size that covers it. `Sector.covVers` (`Impl.lean:853`) drops the
first version of a fresh sector; `CovCand` (`:858`) and `CrashFile` (`512 * n < sz → CovCand`)
enforce it. For a file synced at 4096 bytes, sector 8 (page 1) is fresh with `vers = [zeros]`;
`pwrite(07, off 4096)` makes `vers = [zeros, 07…]`, still fresh; a crash with size 4097 must then
give sector 8 = `07…`. The header justifies it: "ext4 (`data=ordered`) allocates a block a file did
not have at writeback, in the transaction that commits the size covering it, its data written
first".

**The Linux behaviour.** "Its data written first" holds only when the block is allocated
*written*. With `dioread_nolock` (default for ext4 with block size = page size since 5.6, and on
this machine's root filesystem: `/proc/fs/ext4/vda1/options`), writeback maps new blocks as
*unwritten* (`mpage_map_one_extent`: `EXT4_GET_BLOCKS_UNWRIT_EXT`, `fs/ext4/inode.c:2380-2394`).
`ext4_map_blocks` puts a freshly allocated range on the transaction's ordered-data list only if it
is not unwritten (`inode.c:837-851`: `!(map->m_flags & EXT4_MAP_UNWRITTEN)`). The same writeback
handle then raises `i_disksize` and marks the inode dirty (`mpage_map_and_submit_extent`,
`update_disksize:`, `inode.c:2528-2556`). The unwritten-to-written conversion happens later, at I/O
completion, in the io_end's reserved handle; jbd2 does not wait for reserved handles when it
commits (only `jbd2_journal_lock_updates` does, `transaction.c:866-871`). So the transaction holding
the extent (unwritten) and the new size can commit while the data write is still in flight. After
a crash there, the size covers the block and the block reads zeros.

**Execution (tested).** `unwritten.sh` (below): ext4 `-b 4096`, default options plus
`data=ordered,commit=1`; a dm table routes the journal's blocks linearly and every other block
through `dm-delay` (writes held 20 s; reads and flushes not), so commits reach the image and data
does not. A synced 4096-byte file of zeros; `pwrite 07` at 4096; `sync_file_range` starts the
writeback; 4 s later the backing file is copied (the crash) and recovered with `e2fsck`:

| mount | live (filefrag) | crash image after recovery |
|---|---|---|
| default (`dioread_nolock`) | size 4097; block 1 allocated, `unwritten` | **size 4097, extent `Uninit`, byte 4096 = `00`** |
| `dioread_lock` | size 4097; block 1 allocated | size 4096 (the commit waited for the data) |
| default, empty synced file, `pwrite 07` at 0 (`data_ordered_growth.go`'s case) | size 1; block 0 allocated, `unwritten` | **size 1, extent `Uninit`, byte 0 = `00`** |

The outputs are under "Scripts". The default runs give exactly the outcome the model
excludes: size 4097 covers fresh sector 8, and the sector is its first version (zeros), not the
write's.

Why rounds 1-3's tests (`fs-v2-f3/ordered.sh`, `delay.sh`) missed it: both started from a one-byte
file. Extending it zeroes the tail of block 0 (`ext4_block_zero_page_range`'s
`ext4_jbd2_inode_add_write`, `inode.c:4101`), which puts the inode on the ordered list for block 0,
and jbd2's commit then waits for that data (a `TRACE=1` run shows the commit thread in
`ext4_writepages ino 13 range 1-4095 sync_mode 1` from `jbd2_commit_flushing`); with every data
write delayed, nothing committed in the window ("size 1, no extent"). `ordered.sh` switched
periodic writeback off, so no writeback (and no allocation) happened at all. With a block-aligned
size (no tail to zero) the commit has no ordered data to wait for. Note also that with a partial
last block the race is only narrower, not gone: the commit waits for block 0's write, not block 1's.

**A Go program the model proves and Linux breaks.** A root holding `f`, 4096 bytes, durable
(`FsInit`). The boot program: `fi := f.Stat(); if fi.Size() > 4096 { ReadAt(b, 4096); if b[0] != 7 {
panic } } else { f.WriteAt([]byte{7}, 4096) }` (no sync). In the model every crash with size 4097
has byte 4096 = 7 (`CovCand`), so the panic is provably dead; on ext4 with default options the
second boot after the crash above reads 0 and panics.

**Clients.** minibolt's proof uses the rule: `CrashOk.lean`'s `slotCand` keeps a meta slot's
durable version only `¬ FreshCovS` (`:73-85`), and `CrashGood.lean`'s `RawOk` relies on it for a
short file grown by `init`. The real outcome U1 adds is a zero sector, which is not a valid meta
(magic 0) and not a root page `bootOk` accepts as a value, and `Open` re-inits when neither meta is
valid; so `BootCrashSafety`'s conclusion very probably survives, but its proof would have to be
redone over the corrected rule. crashlog and walfs do not use `fresh` (walfs's `Segment`
`fallocate`s first, giving the sectors zero versions; crashlog's flag lands in a non-fresh page).

**Proposed fix (model change).** A covered fresh sector may also be zero: `Sector.covVers s := if
s.fresh then zeroSec :: s.vers.tail else s.vers` (an unwritten extent reads as zeros; ext4 never
exposes the *stale* first version, which is what minibolt needs excluded: the stale bytes a crash
left past the size). Keep the rest of "Ordered growth". The alternative, an environment assumption
"ext4 is mounted with `dioread_lock` (or without delalloc)", excludes the default configuration
and so most real deployments. Update `data_ordered_growth.go` ("Excluded: size 4096 of zeros" is
what ext4 does) and the header sentence quoted above.

### N1 (too-strong assumption): a short atomic copy commits a mid-page prefix that writeback can take

**The premise.** `NoTearCrash` (`NoTear.lean:79-86`): at a crash, each sector a write in flight
touches is one of its versions or the write's prefix of a *page cut* `k` (none, all, or ending on
a 4096-byte file page boundary). The docstring (`:30-41`) argues that writeback cannot see a page
in the middle of its copy, and that `EFAULT` "cannot happen on Go memory, mapped and resident".

**The Linux behaviour.** `generic_perform_write` (`mm/filemap.c:4296-4386`, v7.0, used by ext4)
copies with page faults disabled (`copy_folio_from_iter_atomic`) and does *not* fault the source in
first: it faults in only after a copy came up short. If the copy stops at a source page that is
not present, `write_end` commits the copied prefix when the folio is uptodate (an overwrite of
cached data; `block_write_end` drops it only for a non-uptodate folio), unlocks the folio, and the
loop continues; the next copy fails at the same source page (status 0), the source is faulted in,
and the copy resumes. Between those points the file page holds a prefix that ends where the
*source* page ends, at any file offset, and the folio is unlocked and dirty: writeback (the flusher,
or an `fsync` from another thread, which takes no inode lock in `ext4_sync_file`) can write it. A
source page is not present when it was never touched (a fresh Go heap span: Go does not zero
memory fresh from the OS), swapped out, under a NUMA-balancing hinting fault, being migrated or
compacted, or a not-yet-faulted page of a file mapping (a `WriteTo`-style copy from an `mmap`).
"Resident" is not something Go memory guarantees.

**Execution (tested).** `tear.c`/`tear.sh` (below) make the missing source page with
`userfaultfd` (which only stretches the window from microseconds to seconds): an 8192-byte file of
`A`, fsync'd; a thread `pwrite`s 4096 bytes of `B` at offset 0 from a buffer starting 2148 bytes
into a present page, the next page missing. On ext4:

```
writer held at a fault on source offset 1948
while pwrite is in flight, the page reads 1948 bytes 'B' then 'A' to its end
fsync in flight: ok
pwrite returned 4096
crash image after recovery: size 8192; page 0:  B... A... A ; B bytes: 1948
```

The crash image holds a 1948-byte prefix: mid-page and mid-sector (1948 = 3·512 + 412). It is a
`Landed` prefix, so the base `OsCrash` has it; `NoTearCrash` excludes it. On xfs the same run kept
the old page (`B bytes: 0`): `iomap_write_iter` faults the source in before the copy
(`fs/iomap/buffered-io.c:1139`), so userfaultfd blocks it before anything is copied; on xfs the
window remains only for a page lost between that prefault and the copy (reclaim, migration), which
was not reproduced. (A concurrent `pread` of the page also blocks on xfs, `XFS_IOLOCK_SHARED`.)

**Clients.** `BootCrashSafety` is the only result over the filter. minibolt's `WriteAt` buffers
are page-aligned (`make([]byte, 4096)` and `make([]byte, 4*4096)` are size classes 4096 and 16384,
each object page-aligned in its span) at page-aligned offsets, so a source page boundary is a file
page boundary and the cut is a page cut. This rests on Go's allocator layout and on x86's
`copy_user` stopping exactly at the faulting page (it did here), neither of which the premise
states.

**Proposed fix.** State the premise for what Linux does: a cut is a file page boundary *or* a point
where the source buffer crosses a page boundary. The model does not see the buffer's address, so
either (a) restrict `NoTearStep`/`NoTearCrash` to writes whose buffer address ≡ `off` (mod 4096),
passing `addr % 4096` from the trusted `WriteAt` model (the slice's `Loc` is available there) into
`PWriteStart`; or (b) keep the premise as is but name the assumption it encodes, "every buffer
passed to `pwrite` is congruent to its offset mod 4096", and discharge it for minibolt from Go's
size classes. Correct the docstring: the issue is not `EFAULT` but a short copy that is committed
and later completed.

### N2 (too-strong assumption): a write shortened by `RLIMIT_FSIZE` or `s_maxbytes` ends inside a page

**The premise.** `NoTearStep` (`NoTear.lean:62-66`): a `PWriteFinish` lands and returns a page cut,
and nothing with a nonzero errno. For a page-aligned one-page write that means all or nothing.

**The Linux behaviour.** `generic_write_check_limits` (`mm/filemap.c:1711-1724`) shortens the
count to `limit - pos` for `RLIMIT_FSIZE`, and `generic_write_checks_count` does the same for
`s_maxbytes`. `RLIMIT_FSIZE` is set in 1 KiB units by `ulimit -f`, so any odd value is not a page
multiple. ext4's `s_maxbytes` is `(2^32 - 1) << blkbits` (`ext4_max_size`, `fs/ext4/super.c:3432-
3460`), 3072 bytes past a page boundary with 1 KiB blocks and 2048 with 2 KiB blocks; the header
admits both ("Block size at most 4096 bytes"). Go ignores `SIGXFSZ` (`runtime/sigtab_linux_generic.go`:
`_SigNotify` only), and `poll.FD.Pwrite` retries the rest, which fails with `EFBIG`; `WriteAt`
returns `(0, EFBIG)`.

**Execution (tested).** `efbig/main.go` writes 4096 bytes of `0xAA` at a page-aligned offset and
panics if the write failed but its first byte is now `0xAA`:

```
$ ulimit -f 6; efbig /tmp/r4efbig.dat 4096
WriteAt(4096 bytes at 4096) = 0, write /tmp/r4efbig.dat: file too large
panic: a failed one-page WriteAt wrote part of its page (size now 6144)
$ maxbytes.sh /tmp/r4m 1024       # ext4 -b 1024, OFF = 4 TiB - 4096
WriteAt(4096 bytes at 4398046507008) = 0, write /tmp/r4m/mnt/f: file too large
panic: a failed one-page WriteAt wrote part of its page (size now 4398046510080)
$ maxbytes.sh /tmp/r4m 2048       # ext4 -b 2048
... panic: ... (size now 8796093020160)
```

Under `NoTearStep` the model's `PWriteFinish` returns 0 or 4096 for this write, so the program has
a no-panic proof. The run lies outside the filtered semantics, so `BootCrashSafety` is not refuted
by it (minibolt writes below 1 GiB, and a short `WriteAt` only makes it stop), but the premise is
stated as a property of Linux and is false there.

**Proposed fix (environment assumption).** Add to the no-tear premise's statement (and the
semantics header): "`RLIMIT_FSIZE` is unlimited or a multiple of 4096, and no write ends past the
filesystem's maximum file size rounded down to a page (ext4 with 4 KiB blocks; xfs)". The same
correction is needed on origin/lean: its D22 wording says "the filesystem's own `s_maxbytes` is
page-aligned", which is false for ext4 with 1 KiB or 2 KiB blocks.

### M1 (unsound, unreachable by current clients): `os.File.Write` returns 0 with its error

**The model.** `File.Write.impl` (`TrustedCode/os.lean:384-400`) returns the result of
`WriteAt.impl`, which is `(len, nil)` or `(0, err)`; its docstring says "Go's `Write` gives too:
`len(b)` and nil, or an error".

**Go 1.27.3.** `(*File).Write` (`os/file.go:211-230`) returns `n, e := f.write(b)`, and
`poll.FD.Write` (`internal/poll/fd_unix.go:365-405`) returns `nn, err` with `nn` the bytes already
written when a later `write(2)` fails. (`WriteAt` is different: its own loop discards `m` on an
error, so `(0, err)` is right there.) With a short `write(2)` then a failing one (ENOSPC part way,
`RLIMIT_FSIZE`, `EFBIG`), Go returns a positive count with the error.

**Execution (tested).** `shortwrite/main.go`: `n, err := f.Write(make([]byte, 8192))`; panics if
`err != nil && n != 0`. Under `ulimit -f 6`: `Write(8192 bytes) = 6144, write ...: file too large`,
then the panic. The model proves the panic dead (the base semantics allows the same short-then-
failing `PWriteFinish` pair; only the returned count is wrong).

**Clients.** `seglog.go` calls `f.Write(rec)` and ignores `n`. **Fix:** `Write.impl` returns `nn`
(its own loop of `PWriteStart`/`PWriteFinish`, as `WriteAt.impl`'s, returning the count with the
error), and the offset after an error stays unknown, as now.

### D1 (doc-only)

- `examples/osfs/semantics/data_ordered_growth.go`: "Excluded: size 4096 of zeros ... which ext4
  never does" is ext4's default behaviour (U1). Its evidence line cites `delay.sh`'s "a crash kept
  size 1 and no extent", which is the tail-zeroing artefact explained in U1.
- `Impl.lean`'s header, "Ordered growth": "allocates a block ... its data written first" (U1); and
  "Block size at most 4096 bytes" admits the `s_maxbytes` case of N2.
- `NoTear.lean`'s docstring and `semantics/notear.go`: the `EFAULT` argument (N1); no mention of
  `RLIMIT_FSIZE`/`s_maxbytes` (N2); "large folios ... to be checked": checked, `chunk =
  mapping_max_folio_size` is folio-aligned, so fatal-signal and `write_begin` cuts stay on page
  boundaries; only N1's committed short copy cuts elsewhere.
- `walfs/Results.lean`'s `crash_safety` docstring: "a crash of the machine, or of the process
  alone ... however many times the node crashes or the process restarts" should say that a process
  restart counts only under the header's "Restarts" assumption (a `sync(2)` before the restart).

### O1 (informational): `Hinit_wp` is a hypothesis about opaque constants

Every result takes `Hinit_wp : {{ ownGoState ∅ }} initialize' #() {{ RET #(); True }}` (for
bboltfs inside `NoTearCtx`). On this branch `Code/os.lean`'s initializer runs `axiom`-declared
values (`axiom Stderr.init : val`, `:417`, and the other untranslated initializers), so the triple is
neither provable nor refutable: it is consistent (not vacuous), but it is an unchecked claim that
the real `os`/`syscall` initializers run without panicking or getting stuck. origin/lean's
`os-init-lean` models are what would turn it into a theorem; until then it belongs in each result's
list of assumptions (it is in their docstrings).

## What origin/lean's changes mean for fs-v2

`git log 1fbbd2504b..origin/lean -- GooseLang/Ext/OsFs/Impl.lean TrustedCode/{os,syscall}.lean`:

- **`RLIMIT_FSIZE` hypothesis (`52c027cd63`)**: needed by fs-v2, for the no-tear premises only (the
  base `Fs` semantics allows any short write, so it is sound without it). Take it with N2's
  correction: `s_maxbytes` is not page-aligned on ext4 with 1-2 KiB blocks, on either branch.
- **D22, one aligned page written all-or-nothing in-process (`52c027cd63`)**: not needed by fs-v2's
  semantics; `NoTearStep` is its fs-v2 counterpart (and implies it for in-page writes). Its argument
  shares N2's gap; N1 does not affect it (the call's return is whole; only concurrent observers and
  crashes see the committed short copy).
- **netpollinit fatal error (`56ed68a78b`)**: fs-v2's `Open` has the same gap (Go may die with
  `fatal error: runtime: netpollinit failed` at the first `os.OpenFile`). For the crash-safety
  results here it is covered: a process that dies is, under fs-v2's "Restarts" assumption, a crash
  point (the model's crash may keep everything, and the next generation starts after the `sync`).
  State that in the header ("a process that exits, by a fatal error included, ...") rather than
  adding a model outcome; a crash-free result would need the outcome.
- **os initializer models (`4e748fc69d`, `f7b2a837dd`, `0b733579df`)**: fs-v2 needs them to
  discharge `Hinit_wp` (O1); they model `Stderr` etc., independent of the file extension, so they
  should merge unchanged once `Code/os.toml`'s fs-v2 list is reconciled.

## Attacks the model survived

- **Restarts are machine crashes.** The crash that keeps everything exists from every state:
  `S` = all entries is closed and contains `committed`; `sz = f.size ∈ [sizeLo, sizeHi]`; each
  sector's last version is a `SecCand`, and a `CovCand` (a covered fresh sector has been hit by a
  change, so `vers.tail` holds its last version). Unlinked open files and `ProcState` vanish, as on
  exit. Sound given the `sync` before restart.
- **The filters are not vacuous.** `noTearStep_keeps` gives a `NoTearStep` step wherever `FsStep`
  has one, so `RealNotStuck` over the filtered semantics means what it says. A crash satisfying
  `OsCrash ∧ NoTearCrash` exists from every state (the one above: each sector's last version is in
  its `vers`), so the filter never removes every crash.
- **Ordered growth on xfs** (reasoned from v7.0 source, not re-measured): xfs sets the on-disk size
  at I/O completion (`xfs_end_ioend`), and a truncate-up writes its zeroing back before logging
  the size, so a covering size never precedes the data, post-EOF speculative preallocation
  included. The ext4 `dioread_lock`, `nodelalloc` and `data=journal` paths order data before the
  size (the `dioread_lock` row of U1, measured).
- **"No block past the last page after a crash"** on ext4: allocation and `i_disksize` are in one
  writeback handle (`mpage_map_and_submit_extent`), so a crash cannot keep a block without the size
  covering it; a shrink's blocks go by orphan cleanup at mount. `FsInit`'s `∃ vs sz kp` lets a real
  boot state with post-EOF blocks be represented (`kp = true`).
- **`os.Rename`'s second `lstat`** (of `oldname`, after the model's `LstatDir` token has ended) walks
  a path outside any `CallBegin` window, so a directory rename may overlap it. Its only effects are
  the errno and `SameFile`'s "proceed to `rename(2)`", both covered: `LstatDir` may answer `isDir =
  0` for a directory (the model then goes on to `rename(2)`), and the error branch returns any
  errno.
- **The models against go1.27.3 and x/sys v0.48.0**: `OpenFile` (`openFileNolog`, `newFile` marks
  regular files and directories not pollable), `ReadAt`/`WriteAt` (the loops, `maxRW`, `EINTR`),
  `Read`, `Seek`, `Truncate`, `Sync`, `Close`, `Stat`, `Remove` (unlink then rmdir, `ENOTDIR`
  choice), `Mkdir`, `Readdirnames(n ≤ 0)`, `Fdatasync`, `Flock`; `unix.Mmap`/`Munmap` (the
  `mmapper` checks), `Madvise`, `Fallocate` (modes 0 and `KEEP_SIZE`; a gap before `off` and an
  allocation inside the file both read as zeros in the model), `FcntlFlock` (returns `errno`
  directly, equal as an interface value to `errnoErr`'s). Only M1 differs.
- **`etc/goose.py`'s `walfs`**: a local project whose `lean_roots` send `os`, `syscall`,
  `golang.org/x/sys` and `io/fs` to the empty root, so it reuses project bboltfs's trusted
  translations and owns only `examples/osfs/walfs`.
- **Large folios** (`NoTear`): see D1.

## Not tried

- No Lean counterexample (U1's boot program is a two-branch Go program; its proof over `CovCand`
  would be short, but was not built).
- U1 on ext4 with 1 KiB blocks (`dioread_nolock` is off there), and with `journal_checksum`/
  `fast_commit` variants (excluded by the header anyway). N1 on xfs with real reclaim or NUMA
  migration (no NUMA here, `kernel.numa_balancing = 0`, no swap).
- The metadata half (`Follows`, `CallBegin`, `Needed`) and journal ordering of metadata calls
  were not re-attacked or measured (rounds 2-3 argued them; still not measured).
- Whether minibolt's proof goes through over U1's corrected rule.

## Summary

| # | severity | what | evidence | fix |
|---|---|---|---|---|
| U1 | unsound | ordered growth false under ext4 `dioread_nolock` (default): covering size, block reads zeros | tested; kernel source | `covVers` of a fresh sector also allows `zeroSec`; update header and `data_ordered_growth.go` |
| N1 | too-strong assumption | `NoTearCrash`: a committed short copy cuts at a source page boundary, mid-page | tested (ext4, userfaultfd); xfs reasoned | cut at file or source page boundary; pass `addr % 4096` or assume congruent buffers |
| N2 | too-strong assumption | `NoTearStep`/`NoTearCrash`: `RLIMIT_FSIZE`, ext4 1-2 KiB `s_maxbytes` cut a page | tested (Go) | environment hypothesis; fix origin/lean's D22 wording too |
| M1 | unsound, unreachable by clients | `File.Write` returns 0 with its error; Go returns `nn` | tested (Go) | return the loop's count |
| D1 | doc-only | example, header, `NoTear` and walfs docstrings | read | reword |
| O1 | informational | `Hinit_wp` over axiomatized initializers | read | discharge with origin/lean's init models |

## Scripts

All run from `.lake/review-r4/` (untracked), as root through `sudo` where they touch devices.
`fetch.sh` fetched the v7.0 kernel files cited above from the `torvalds/linux` mirror.

### `unwritten.sh` (U1)

Runs: `INIT=4096 unwritten.sh /tmp/r4v` (default options), `INIT=4096 unwritten.sh /tmp/r4w
dioread_lock`, `INIT=0 unwritten.sh /tmp/r4x "" 0`. Outputs:

```
# INIT=4096, default (dioread_nolock)
live: size 4097;  0: 0.. 0: 4171.. 4171: 1: ; 1: 1.. 1: 37376.. 37376: 1: 4172: last,unwritten,eof;
e2fsck exit 1
crash image: size 4097; extents:  0/ 0 1/ 2 0 - 0 4171 - 4171 1 ; 0/ 0 2/ 2 1 - 1 37376 - 37376 1 Uninit;
after recovery: size 4097, byte 0:  00, byte 4096:  00
# INIT=4096, dioread_lock
live: size 4097;  0: 0.. 0: 4171.. 4171: 1: ; 1: 1.. 1: 4683.. 4683: 1: 4172: last,eof;
e2fsck exit 1
crash image: size 4096; extents:  0/ 0 1/ 1 0 - 0 4171 - 4171 1 ;
after recovery: size 4096, byte 0:  00, byte 4096:
# INIT=0, pwrite 07 at 0 (an empty synced file: data_ordered_growth.go's case)
live: size 1;  0: 0.. 0: 37376.. 37376: 1: last,unwritten,eof;
e2fsck exit 1
crash image: size 1; extents:  0/ 0 1/ 1 0 - 0 37376 - 37376 1 Uninit;
after recovery: size 1, byte 0:  00, byte 0:  00
```

```bash
#!/bin/bash
# fs-v2-r4, finding U1: does ext4 (default options: delalloc, dioread_nolock) commit the size that
# covers a NEW block, and the block's (unwritten) extent, before the block's data is on disk?
# If so, a crash recovers the new size with zeros in the new block: the "first version" of a
# fresh sector under a size that covers it, which Impl.lean's ordered-growth rule excludes.
#
# Usage: unwritten.sh WORKDIR [MOUNTOPTS] [OFF]
#   MOUNTOPTS: extra ext4 mount options (e.g. dioread_lock), default none
#   OFF: where the one-byte append 07 goes (default 4096: a new block)
# INIT=N in the environment: the synced file holds N zero bytes first (default 1; 4096: no partial
#   last block, so no tail zeroing joins the commit as ordered data)
# One device, internal journal. A dm table maps the journal's blocks linearly and every other
# block through dm-delay (writes delayed $DELAY ms, reads and flushes not), so the journal's
# commits reach the backing file at once and the data does not. A copy of the backing file taken
# then is the crash; e2fsck replays its journal.
set -u
D=${1:?workdir}
EXTRA=${2:-}
OFF=${3:-4096}
DELAY=${DELAY:-20000}
mkdir -p "$D/mnt" "$D/mnt2"
IMG=$D/u.img
sudo umount "$D/mnt" 2>/dev/null; sudo dmsetup remove r4delay 2>/dev/null
rm -f "$IMG" "$IMG.crash"; truncate -s 256M "$IMG"
L=$(sudo losetup --find --show "$IMG")
sudo mkfs.ext4 -q -F -b 4096 "$L"
# the journal's extent (inode 8), in 4 KiB blocks
J=$(sudo debugfs -R "ex <8>" "$L" 2>/dev/null | awk 'NR>1 && $0 ~ /-/ {print}' | head -1)
JS=$(echo "$J" | awk '{print $(NF-3)}')
JE=$(echo "$J" | awk '{print $(NF-1)}')
[ -z "$JS" ] && { echo "no journal extent: $J"; exit 1; }
TOT=$(sudo blockdev --getsz "$L")
S0=$((JS*8)); S1=$(((JE+1)*8))
echo "journal blocks $JS-$JE (sectors $S0-$S1 of $TOT)"
sudo dmsetup create r4delay <<EOF
0 $S0 delay $L 0 0 $L 0 $DELAY $L 0 0
$S0 $((S1-S0)) linear $L $S0
$S1 $((TOT-S1)) delay $L $S1 0 $L $S1 $DELAY $L $S1 0
EOF
OPTS=data=ordered,commit=1${EXTRA:+,$EXTRA}
sudo mount -o "$OPTS" /dev/mapper/r4delay "$D/mnt"
grep r4delay /proc/mounts
sudo chmod 777 "$D/mnt"
F=$D/mnt/f
head -c "${INIT:-1}" /dev/zero > "$F"; sync "$F"; sudo sync
python3 -c "import time; time.sleep($DELAY/1000+2)"
OLD=$(cat /proc/sys/vm/dirty_writeback_centisecs)
sudo sysctl -q vm.dirty_writeback_centisecs=0
T=/sys/kernel/tracing
if [ "${TRACE:-0}" = 1 ]; then
  echo | sudo tee $T/trace >/dev/null; for e in jbd2/jbd2_start_commit jbd2/jbd2_commit_locking jbd2/jbd2_commit_flushing jbd2/jbd2_end_commit jbd2/jbd2_handle_start jbd2/jbd2_handle_stats ext4/ext4_da_write_pages ext4/ext4_writepages; do echo 1 | sudo tee $T/events/$e/enable >/dev/null; done
fi
xfs_io -c "pwrite -S 0x07 $OFF 1" "$F" >/dev/null
xfs_io -c "sync_range -w 0 0" "$F"
python3 -c 'import time; time.sleep(4)'
echo "live: size $(stat -c %s "$F"); $(sudo filefrag -v "$F" | grep -E '^ +[0-9]+:' | tr -s ' ' | tr '\n' ';')"
sudo cp "$IMG" "$IMG.crash"
if [ "${TRACE:-0}" = 1 ]; then
  for e in jbd2 ext4; do echo 0 | sudo tee $T/events/$e/enable >/dev/null; done
  sudo cat $T/trace | grep -v '^#' | tail -40
  sudo cat /proc/fs/jbd2/dm-*/info 2>/dev/null | head -5
fi
sudo sysctl -q vm.dirty_writeback_centisecs="$OLD"
sudo umount "$D/mnt"; sudo dmsetup remove r4delay; sudo losetup -d "$L"
L2=$(sudo losetup --find --show "$IMG.crash")
sudo e2fsck -fy "$L2" >/dev/null 2>&1; echo "e2fsck exit $?"
echo "crash image: size $(sudo debugfs -R 'stat /f' "$L2" 2>/dev/null | awk '/Size:/ {print $NF; exit}'); extents: $(sudo debugfs -R 'ex /f' "$L2" 2>/dev/null | tail -n +2 | tr -s ' ' | tr '\n' ';')"
sudo mount "$L2" "$D/mnt2"
F2=$D/mnt2/f
echo "after recovery: size $(stat -c %s "$F2"), byte 0: $(od -An -tx1 -N1 "$F2"), byte $OFF: $(od -An -tx1 -j"$OFF" -N1 "$F2")"
sudo umount "$D/mnt2"; sudo losetup -d "$L2"
```

### `tear.c`, `tear.sh` (N1)

Build: `gcc -O1 -pthread -o tear tear.c`. Run: `tear.sh /tmp/r4t ext4`, `tear.sh /tmp/r4t xfs`.

```c
// fs-v2-r4, finding N1: a buffered pwrite(2) whose source buffer has a page the kernel cannot
// read without a fault commits a prefix ending where the source page ends (mid-page and
// mid-sector in the file), and that prefix is visible and can be written back before the call
// returns. NoTear.lean's premises (NoTearCrash: a write in flight is cut only at a file page
// boundary) exclude this state at a crash.
//
// The missing source page is made by userfaultfd (MISSING mode), which holds the writer in its
// fault-in for as long as we like; on a real system the same short atomic copy happens on any
// source page that is not present: never touched (a fresh Go heap span), swapped out, under a
// NUMA hinting fault or a migration. Userfaultfd only widens the window from microseconds to
// seconds.
//
// Usage: tear FILE [SKEW]   (root, for userfaultfd from kernel-mode faults)
//   FILE is made 8192 bytes of 'A' (fsync'd, so its page cache is uptodate); the writer thread
//   writes 4096 bytes of 'B' at offset 0 from a buffer that starts SKEW bytes (default 2148)
//   into a present page, so its source crosses into the missing page after 4096-SKEW bytes.
//   While the writer is held, the main thread preads the page, fsyncs the file (so the torn page
//   is on disk) and, if $SNAP is set, runs it (e.g. a copy of the device's image: the crash),
//   then releases the writer and prints what pwrite returned.
#define _GNU_SOURCE
#include <fcntl.h>
#include <linux/userfaultfd.h>
#include <poll.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <sys/syscall.h>
#include <unistd.h>

static int fd;
static char *src;
static ssize_t wres;

static void *writer(void *arg) {
  (void)arg;
  wres = pwrite(fd, src, 4096, 0);
  return NULL;
}

int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: tear FILE [SKEW]\n"); return 2; }
  long skew = argc > 2 ? atol(argv[2]) : 2148;
  long pg = sysconf(_SC_PAGESIZE);
  fd = open(argv[1], O_RDWR | O_CREAT | O_TRUNC, 0644);
  if (fd < 0) { perror("open"); return 1; }
  char a[8192];
  memset(a, 'A', sizeof a);
  if (pwrite(fd, a, sizeof a, 0) != (ssize_t)sizeof a) { perror("pwrite A"); return 1; }
  if (fsync(fd)) { perror("fsync"); return 1; }

  char *region = mmap(NULL, 3 * pg, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (region == MAP_FAILED) { perror("mmap"); return 1; }
  memset(region, 'B', pg);  // page 0 present; pages 1, 2 missing
  int uffd = syscall(SYS_userfaultfd, O_CLOEXEC);
  if (uffd < 0) { perror("userfaultfd"); return 1; }
  struct uffdio_api api = {.api = UFFD_API};
  if (ioctl(uffd, UFFDIO_API, &api)) { perror("UFFDIO_API"); return 1; }
  struct uffdio_register reg = {.range = {.start = (unsigned long)(region + pg), .len = 2 * pg},
                                .mode = UFFDIO_REGISTER_MODE_MISSING};
  if (ioctl(uffd, UFFDIO_REGISTER, &reg)) { perror("UFFDIO_REGISTER"); return 1; }
  src = region + skew;

  pthread_t t;
  pthread_create(&t, NULL, writer, NULL);
  struct pollfd p = {.fd = uffd, .events = POLLIN};
  if (poll(&p, 1, 5000) != 1) { fprintf(stderr, "no fault: the writer did not stall\n"); return 1; }
  struct uffd_msg msg;
  if (read(uffd, &msg, sizeof msg) != sizeof msg) { perror("read uffd"); return 1; }
  printf("writer held at a fault on source offset %ld\n",
         (long)(msg.arg.pagefault.address - (unsigned long)src));

  char r[4096];
  int nb = 0;
  // xfs takes the inode's iolock shared for a buffered read, which the writer holds exclusive:
  // NOREAD=1 skips the read in flight (it would wait for the writer)
  const char *noread = getenv("NOREAD");
  if (!(noread && *noread)) {
    if (pread(fd, r, sizeof r, 0) != (ssize_t)sizeof r) { perror("pread"); return 1; }
    while (nb < 4096 && r[nb] == 'B') nb++;
    int rest_a = 1;
    for (int i = nb; i < 4096; i++) if (r[i] != 'A') rest_a = 0;
    printf("while pwrite is in flight, the page reads %d bytes 'B' then %s\n", nb,
           rest_a ? "'A' to its end" : "other bytes");
  }
  if (fsync(fd)) perror("fsync (in flight)"); else printf("fsync in flight: ok\n");
  const char *snap = getenv("SNAP");
  if (snap && *snap) { fflush(stdout); if (system(snap) != 0) fprintf(stderr, "SNAP failed\n"); }

  // release the writer: fill the missing page with 'B'
  char *fill = aligned_alloc(pg, pg);
  memset(fill, 'B', pg);
  struct uffdio_copy cp = {.dst = msg.arg.pagefault.address & ~(pg - 1), .src = (unsigned long)fill,
                           .len = pg};
  if (ioctl(uffd, UFFDIO_COPY, &cp)) { perror("UFFDIO_COPY"); return 1; }
  pthread_join(t, NULL);
  printf("pwrite returned %zd\n", wres);
  if (pread(fd, r, sizeof r, 0) != (ssize_t)sizeof r) { perror("pread"); return 1; }
  nb = 0;
  while (nb < 4096 && r[nb] == 'B') nb++;
  printf("after it returned: %d bytes 'B'\n", nb);
  return 0;
}
```

```bash
#!/bin/bash
# fs-v2-r4, finding N1: a pwrite in flight, held in its source-page fault (tear.c), with the
# torn page fsync'd; a copy of the device image taken then is the crash. Prints what the page
# holds after recovery.
# Usage: tear.sh WORKDIR [ext4|xfs] [SKEW]
set -u
D=${1:?workdir}
FS=${2:-ext4}
SKEW=${3:-2148}
H=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$D/mnt" "$D/mnt2"
IMG=$D/t.$FS
rm -f "$IMG" "$IMG.crash"; truncate -s 512M "$IMG"
L=$(sudo losetup --find --show "$IMG")
if [ "$FS" = ext4 ]; then sudo mkfs.ext4 -q -F -b 4096 "$L"; OPTS=data=ordered
else sudo mkfs.xfs -q -f "$L"; OPTS=nouuid; fi
sudo mount -o $OPTS "$L" "$D/mnt"
echo "$FS: $(grep " $D/mnt " /proc/mounts)"
sudo env SNAP="cp $IMG $IMG.crash" NOREAD=$([ "$FS" = xfs ] && echo 1) "$H/tear" "$D/mnt/f" "$SKEW"
sudo umount "$D/mnt"; sudo losetup -d "$L"
L2=$(sudo losetup --find --show "$IMG.crash")
[ "$FS" = ext4 ] && { sudo e2fsck -fy "$L2" >/dev/null 2>&1; echo "e2fsck exit $?"; }
sudo mount -o $OPTS "$L2" "$D/mnt2"
echo "crash image after recovery: size $(stat -c %s "$D/mnt2/f"); page 0: $(od -An -c -w4096 -N4096 "$D/mnt2/f" | tr -s ' ' | sed 's/\(B \)\{1,\}/B... /; s/\(A \)\{1,\}/A... /') ; B bytes: $(head -c 4096 "$D/mnt2/f" | tr -cd B | wc -c)"
sudo umount "$D/mnt2"; sudo losetup -d "$L2"
```

### `efbig/main.go`, `maxbytes.sh` (N2)

Build: `GOTOOLCHAIN=go1.27.3 go build -o efbig .` (module `r4/efbig`, `go 1.27`).

```go
// fs-v2-r4, finding N2: a one-page, page-aligned WriteAt that fails having written part of the
// page. NoTear.lean's NoTearStep says a pwrite that lands part of its data stops at a page
// boundary, and with a nonzero errno lands nothing; Linux shortens a write that crosses
// RLIMIT_FSIZE or the filesystem's s_maxbytes to end there (generic_write_check_limits), which
// may be inside a page. Go's Pwrite loop then retries the rest and gets EFBIG, so WriteAt
// returns (0, EFBIG) with a prefix of the page written.
//
// Usage: efbig FILE OFF   (writes 4096 bytes of 0xAA at OFF, a multiple of 4096)
// Under `ulimit -f 6` (6144 bytes) with OFF=4096, or on ext4 with 1 KiB blocks
// (s_maxbytes = (2^32-1) << 10) with OFF = 4398046507008 (4 TiB - 4096).
package main

import (
	"fmt"
	"os"
	"strconv"
)

func main() {
	off, _ := strconv.ParseInt(os.Args[2], 10, 64)
	f, err := os.OpenFile(os.Args[1], os.O_RDWR|os.O_CREATE, 0o644)
	if err != nil {
		panic(err)
	}
	buf := make([]byte, 4096)
	for i := range buf {
		buf[i] = 0xAA
	}
	n, err := f.WriteAt(buf, off)
	fmt.Printf("WriteAt(4096 bytes at %d) = %d, %v\n", off, n, err)
	if err != nil {
		b := make([]byte, 1)
		if _, rerr := f.ReadAt(b, off); rerr == nil && b[0] == 0xAA {
			fi, _ := f.Stat()
			panic(fmt.Sprintf("a failed one-page WriteAt wrote part of its page (size now %d)", fi.Size()))
		}
	}
}
```

```bash
#!/bin/bash
# fs-v2-r4, finding N2: ext4 with 1 KiB blocks has s_maxbytes = (2^32-1) << 10, 1 KiB short of a
# page boundary; a page-aligned one-page WriteAt just below it lands 3072 bytes and fails.
# Usage: maxbytes.sh WORKDIR [BLOCKSIZE]
set -u
D=${1:?workdir}
BS=${2:-1024}
H=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$D/mnt"
IMG=$D/m.img
rm -f "$IMG"; truncate -s 64M "$IMG"
L=$(sudo losetup --find --show "$IMG")
sudo mkfs.ext4 -q -F -b "$BS" "$L"
sudo mount "$L" "$D/mnt"; sudo chmod 777 "$D/mnt"
MAX=$(( ((1 << 32) - 1) * BS ))
OFF=$(( (MAX / 4096) * 4096 ))
[ $OFF -eq $MAX ] && OFF=$((OFF - 4096))
echo "ext4 -b $BS: s_maxbytes $MAX ($((MAX % 4096)) past a page boundary); WriteAt at $OFF"
"$H/efbig/efbig" "$D/mnt/f" "$OFF"; echo "exit $?"
echo "size $(stat -c %s "$D/mnt/f")"
sudo umount "$D/mnt"; sudo losetup -d "$L"
```

### `shortwrite/main.go` (M1)

```go
// fs-v2-r4, finding M1: os.File.Write returns the bytes it wrote with its error; the model
// (TrustedCode/os.lean, File.Write.impl, which returns WriteAt's result) returns 0 with any
// error. Under `ulimit -f 6` a Write of 8192 bytes at offset 0 writes 6144 and fails (EFBIG).
// Usage: shortwrite FILE
package main

import (
	"fmt"
	"os"
)

func main() {
	f, err := os.OpenFile(os.Args[1], os.O_RDWR|os.O_CREATE|os.O_TRUNC, 0o644)
	if err != nil {
		panic(err)
	}
	n, err := f.Write(make([]byte, 8192))
	fmt.Printf("Write(8192 bytes) = %d, %v\n", n, err)
	if err != nil && n != 0 {
		panic("Write returned a nonzero count with its error; the model says 0")
	}
}
```
