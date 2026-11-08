# Review: the Linux file extension, version 2 (`GooseLang/Ext/Fs/`)

**Date:** 2026-11-05. **Reviewed:** `GooseLang/Ext/Fs/Paths.lean`, `Tree.lean`, `Impl.lean` at
`41472adc53` (branch `fs-v2`; unchanged at `7f0c1152ba`, which only adds `Tests.lean`): the step
relation `IsFsStep`, the crash relation `OsCrash` (`MachineCrash`, `ProcRestart`), `FsInit`, and the
environment assumptions of `Impl.lean`'s header. The design note `notes/fs-semantics-v2.md` was
read as a set of claims to check. The `os`/`unix` trusted models (`TrustedCode/os.lean`,
`TrustedCode/golang_org/x/sys/unix.lean`) were consulted only for how the operations are used.

**Method.** The `axiom` skill's, adapted to a trusted semantics: the claim under review is that every
behaviour Linux (ext4 `data=ordered`/`data=journal`, or xfs, under the header's environment) can
show for the modelled calls is a behaviour of the model. A finding is an execution (calls, threads,
crash point), the Linux outcome, and why the model excludes it. As the user allowed, no Go test and
no Lean counterexample was built (crashes and writeback failures are hard to trigger). The kernel
claims were checked against Linux v6.12 source (`fs/ext4/{dir,inode,readpage,extents,fsync}.c`,
`fs/ext4/ext4_jbd2.h`, `mm/filemap.c`, `fs/xfs/xfs_bmap_util.c`); where a finding rests on
behaviour that was not read in the source, it says so.

## Verdict

**Not sound as stated: six findings**, none of them in the directory tree or the journal model. The
metadata half (`Tree.lean`, the metadata steps, `dirCommitLen`, readdir, the crash's prefix of the
log, inode freshness) survived every attack tried. The findings are in the data path:

| # | severity | finding | recommendation |
|---|---|---|---|
| F1 | high | after a failed writeback, the model keeps showing the page cache's last version. Linux can drop it: ext4 invalidates the pages, and clean pages can be evicted | environment assumption (no writeback fails), or a model change |
| F2 | medium | `FsInit` makes every file and name durable at the first start. Nothing in the header requires this | environment assumption |
| F3 | refuted by experiment (2026-11-08) | after a machine crash, the model's file is zero past its size. On ext4 the tail of the last block can hold bytes of a write whose size change was lost; the finding was that a later extension exposes them. ext4 7.0 zero-fills every extension instead | none (the model's zeros are right) |
| F4 | low | `pread` always returns everything up to EOF on success. Linux returns a short count with no error when a page allocation fails partway (`ENOMEM`) | model change |
| F5 | low | `ProcRestart` lands an in-flight `fallocate` fully or not at all. ext4 grows the file chunk by chunk, and the call can still fail partway after the process is killed | model change |
| F6 | informational | `PWriteFinish` never returns a short count with errno 0, which Linux does (e.g. on `ENOSPC` partway). Sound for Go programs through the trusted `WriteAt` loop | optional model change |

Separately, under "Stuck or less defined than Linux": the places where a real client (etcd's
WAL, bbolt) would get stuck.

## Findings

### F1 (high): reads, mappings and later writes after a failed writeback

**The model's claim.** A failed `fsync` marks each dirty sector that is not busy as *lost*: its
versions are kept, and its dirty bit is cleared (`OsFile.syncFailed`, `Impl.lean:256-259`; the
`Fsync` failure branch, `Impl.lean:559-560`). After that, every read still sees the sector's **last**
version: `OsFile.contents` (`:107-108`) is what `ReadSees` (`:326-329`), `cellVal` (`:346-350`, the
mapped cells) and `OsFile.change` (`:229-233`, the base of every later write) use. The
header (`:33-35`) and the design note (V5) say "Linux marks them clean". That is right, but only half
the story: a clean page whose writeback failed holds data that is not on disk, and Linux does not
keep it.

**The Linux behaviour.**
- ext4, delayed allocation failing at writeback (`mpage_map_and_submit_extent`, `inode.c:2246-2292`
  in v6.12, "Delayed block allocation failed ... Data will be lost") sets `give_up_on_write`.
  `mpage_release_unused_pages(…, true)` (`inode.c:1552-1600`) then calls `block_invalidate_folio`
  and `folio_clear_uptodate` on the dirty pages. The next read goes to disk.
- For any writeback I/O error (ext4 or xfs), the folio ends writeback clean, with the error recorded in
  the mapping's `errseq`. It can then be reclaimed under memory pressure, and a later read returns the
  disk's contents: the 2018 PostgreSQL "fsyncgate" behaviour, and the ATC'20 study "Can Applications
  Recover from fsync Failures?".
- A background writeback failure, with no `fsync` running, does the same. Its error is reported
  to the next `fsync` of each file description that sampled `errseq` before it. But if the inode
  is evicted while no fd holds it (after a process restart, say), the error and the pages are both
  gone. The next process then reads the old data, and its `fsync` succeeds with nothing to write.

**Execution 1 (within one process).** `f` is a synced file whose sector 0 holds `A`.
`f.WriteAt(B, 0)` succeeds: sector 0 has `vers = [A, B]` and is dirty. `f.Sync()` returns an error
(the model's failure branch, `Impl.lean:559`), and sector 0 is lost with `last = B`. Memory pressure
evicts the page (or ext4 invalidated it). `f.ReadAt(buf, 0)` returns `A` on Linux; `ReadSees` says
`B`. A Go program that panics unless `buf` is `B` panics on Linux and has a proof.
A variant: the program writes byte 0 again. Linux builds the new page from `A` (old bytes `A[1..]`),
but the model builds it from `B`, so after a successful `fsync` and a crash the model guarantees
`B[1..]`, which is not on disk.

**Execution 2 (across a process restart, no failed `fsync` in the model).** `WriteAt(B, 0)` with no
sync: sector 0 is dirty in the model. Background writeback fails: on Linux the page is clean and its
contents are `B`, the disk holds `A`, and the error is not yet seen. The process dies (`ProcRestart`,
`Impl.lean:747-752`: dirty sectors stay dirty). With no fd open, the inode is evicted, taking the
pages and the `errseq`. The next process opens `f` and reads `A` (the model says `B`). Its `Sync()`
returns 0 (the model collapses sector 0 to `[B]`, `Impl.lean:248-252`). After a machine crash, the
model guarantees `B`, but the disk holds `A`.

**Why the environment does not exclude it.** The header (`:20-21`) excludes media errors and
"error or shutdown events". It does not exclude a writeback that fails for another reason: a
transport error or a timeout (not a media error), or delayed allocation's `ENOSPC` when no cluster
is free (ext4's "should not happen"). The model itself expects `fsync` to fail: that is why it has the
failure branch and the dirty bit.

**Recommendation: an environment assumption** (simplest). It makes the lost-sector machinery
unnecessary but harmless (more behaviours). Proposed wording, for the header after "has no media
errors":

> No writeback of a file in the roots' trees fails: the device returns no I/O error, and
> writeback never fails to allocate blocks (ext4's "Delayed block allocation failed"). (Linux
> may drop the page cache's copy of data whose writeback failed, so that reads return the disk's
> older contents; the model does not describe that.)

The alternative is a **model change**, if the proofs are to cover recovery from a failed
`fsync`. Every read of a byte in a lost sector (`ReadSees`; `cellVal` a hole) may return the byte of
any of the sector's versions. A change into a lost sector builds its new version from any of them.
A background writeback failure also needs a nondeterministic step that marks dirty sectors lost,
since no `fsync` runs. The assumption is far simpler; nothing in etcd or bbolt goes on using a file
after its `Sync` fails (etcd's WAL calls `Fatal`, bbolt fails the transaction).

### F2 (medium): `FsInit` assumes everything is durable at the first start

**The model's claim.** `FsInit` (`Impl.lean:760-765`) requires `metaLog = []` (every name
durable) and every file `OsFile.ofBytes c`: one clean version per sector, size range a single point,
so all of it on disk. The header's environment (`:17-18`) says only "the tree at boot is their
trees' entries".

**Execution.** Before the verified program's first run, an operator or tool writes into a root
without syncing: `cp` of a snapshot, `etcdutl snapshot restore` (which syncs, but other tools do
not), an earlier unverified version of the program, or a test harness. The verified program starts
from `FsInit`, reads the file (which matches), and relies on it. The machine loses power. After the
reboot, the file is missing, empty, or holds old contents (data and names not yet written back or
committed). The model's crash keeps every file as it was at `FsInit` (`MachineCrash`, `:735-742`,
with sizes in `[sizeLo, sizeHi]` = the boot size and each sector's only version). A next generation
that assumes "the files the first run read are still there" is wrong on Linux.

**Recommendation: an environment assumption.** Weakening `FsInit` (arbitrary versions and a
non-empty log) would make every client's boot proof deal with a history it cannot know. Proposed
wording:

> When the program first starts, the roots' trees and every file in them are durable: nothing has
> changed them since their last successful `sync`, `syncfs` or `fsync`/directory `fsync` (for
> example, the machine has booted since).

### F3 (refuted by experiment): stale bytes past EOF after a crash, exposed by a later extension (ext4)

**Refuted (2026-11-08).** The stale bytes are on disk, but no extension shows them. Test:
`notes/axiom-review/fs-v2-f3/f3.sh WORKDIR {truncate|write|falloc}` (root; Linux 7.0.0-38-generic,
ext4 `data=ordered,commit=300` on a loop device). A one-byte file `00`, synced; `pwrite 07` at
offset 1, not synced; `sync_file_range` writes the page back without a journal commit; a copy of the
image taken while mounted is the crash; `e2fsck` replays its journal. In the crash image the size is
1 and the file's block holds `00 07` (`debugfs bmap`, raw read): the crash ordering below happens.
After mounting the copy, extending the file to 4 bytes reads:

| extension | bytes 0-3 |
|---|---|
| `ftruncate(4)` | `00 00 00 00` |
| `pwrite(09, off 3)` | `00 00 00 09` |
| `fallocate(0, 4)` | `00 00 00 00` |

Every extension zero-fills from the old size (as POSIX requires), so the analysis below of the
extend paths was wrong for this kernel (current ext4 zeroes the partial block on extension). The
model change F3 led to (`CrashFile` keeping whole sectors, `resized` filling from `rawAt`) was
reverted: an extension fills with zeros. What the experiment does show is that a crash recovers
the old size with the new data on disk; with `data=ordered` the converse (a larger size with data
older than it) cannot happen, which the crash rule now requires (`Impl.lean`, `CrashFile`).

The original finding, kept for the record:


**The model's claim.** `MachineCrash` makes each surviving file `OsFile.ofBytes img`
(`Impl.lean:741`, `:102-104`): every byte past `img.length` is a clean zero. An extension after the
crash adds zero versions to the sectors from the old size on (`OsFile.truncate`, `:242-243`;
`landWrite`'s gap, `:237-239`). Reads of the extended range therefore see zeros.

**The Linux behaviour (ext4).** ext4 relies on the on-disk tail of a file's last block past
`i_size` being zero: writeback zeroes the part of the page past `i_size`, and truncation zeroes the
partial block. A crash can break that:
- An append of `D` at `[L, L+k)` lands inside the last, already allocated block.
- Writeback writes the block, with `D` (in-memory `i_size` is `L+k`, so nothing is zeroed).
- The journal transaction carrying `i_disksize = L+k` has not committed when the power goes.

After the crash, the size is `L`, which the model allows (`CrashImage`'s size range), and the
block's bytes past `L` are `D`. The read path does not hide them: `ext4_mpage_readpages`
(`readpage.c:250-325`) zeroes only blocks wholly past EOF and reads the partial last block in full.
v6.12's `ext4_setattr` does not zero the old tail when extending: it only calls
`pagecache_isize_extended`, for mmap. So `ftruncate(L+512)` and then `pread(L, 512)` returns `D`
where the model says zeros. A buffered write past EOF that starts inside that block leaves the gap
between `L` and the write holding `D`, because `__block_write_begin` reads the mapped block and the
copy covers only the written range.

**Confidence.** The read and extend paths were read in the source; the crash ordering (writeback
before the size commit, and no zeroing anywhere else) was not reproduced. Upstream has discussed
zeroing the partial block past EOF when extending; which kernels have it was not checked. xfs
zeroes from the old EOF on extension (`xfs_file_write_zero_eof`, `iomap_zero_range`), so the
finding is ext4's.

**Execution (Go).** Append 100 bytes `D` at offset `L = 1000` of a synced 1000-byte file, with no
sync. Crash; the file comes back with size 1000. `Truncate(2000)`, then `ReadAt(buf, 1000)`, then
`if buf[0] != 0 { panic }`.

**Recommendation: a model change**, small. In `MachineCrash`, the surviving file keeps for every
sector the version `CrashImage` chose for it (or zeros, for sectors wholly past the size), uncut,
instead of `secOf img n`. The size is `img.length` and `contents` cuts to it, so reads up to the
size are unchanged; an extension then shows the kept version's bytes past the old size. (Being
more permissive than ext4 past the last block is sound.) bbolt and the WAL extend files with
`ftruncate`/`fallocate` and read the extension (the WAL's preallocated segment tail, checked for
zeros by `isTornEntry`). Their proofs would then need the bytes past a recovered size to be
unknown, which is the truth on ext4. An environment assumption would have to name a kernel that
zeroes the tail, and none was identified.

### F4 (low): short `pread` without an error

**The model's claim.** A successful `PRead` returns `min n (sz − off)` bytes for a size `sz`
`fstat` could see (`ReadSees`, `Impl.lean:326-329`; `PRead`, `:516-519`). With no change in flight,
that is everything up to EOF.

**The Linux behaviour.** `filemap_read` (`mm/filemap.c`, v6.12) loops over page batches and
`return already_read ? already_read : error`. If `filemap_get_pages` fails after the first batch
(`-ENOMEM` when allocating a page for readahead), the call returns a short count with no error,
before EOF.

**Execution.** A 1 MiB file. `f.Read(buf)` with `len(buf) = 1 MiB`: Go's `File.Read` makes one
`read(2)`, and the trusted model one `PRead` (`TrustedCode/os.lean`, `File.Read.impl`). Under memory
pressure Linux returns 256 KiB and `nil`. The model guarantees `n = 1 MiB`, so a program checking
`n == len(buf)` (wrongly, by `io.Reader`'s contract, but provably in the model) panics. `ReadAt` is
unaffected, since its loop retries short reads in both Go and the model.

**Recommendation: a model change.** On success, any non-empty prefix of a `ReadSees` result (the
empty result only when the full result is empty):
`e' = osRes (#(r.take k)) 0 ∧ (0 < k ∨ r = [])`.

### F5 (low): a process restart during `fallocate`

**The model's claim.** `ProcRestart` (`Impl.lean:747-752`) lands each change in flight by `Landed`
(`:263-271`). A `.truncate` change, which is how `fallocate`'s growth is represented
(`FallocStart`, `:676-680`), is either applied or not. But `FallocFinish`'s own failure branch
(`:686-688`) allows any size between, because ext4 grows the file as each chunk is allocated.

**The Linux behaviour.** `ext4_alloc_file_blocks` (`extents.c`, v6.12) loops over chunks, each in
its own handle, and calls `ext4_update_inode_size(inode, epos)` after each one. The loop does not
check for a fatal signal. A process killed while a thread is in it does not stop the call: the call
runs on, and can fail with `ENOSPC` partway, leaving an intermediate size. (`MachineCrash` covers
the intermediate size through `CrashImage`'s range. xfs sets the size only after the whole
allocation, so it is not affected.)

**Execution.** A thread is in `unix.Fallocate(fd, 0, 0, 1<<30)` on an empty file when the process
is killed. The filesystem fills after 256 MiB, so the file is 256 MiB. The next generation's
`Stat().Size()` is 256 MiB on Linux; the model allows only 0 or 1 GiB.

**Recommendation: a model change.** `Landed`'s case for a resize also allows any size between the
file's size and the target, zero-filled (as `FallocFinish`'s failure branch does). This adds
behaviours to `ftruncate`, whose resize is atomic in Linux, which is sound. Or give `fallocate` a
change kind of its own.

### F6 (informational): a short `pwrite` with errno 0

`PWriteFinish` (`Impl.lean:530-534`) pairs errno 0 with all of the data. Linux's
`generic_perform_write` returns a positive short count (no error) when it stops partway, for
example on `ENOSPC` or `EFBIG`. Taken on its own, the step lacks that outcome. Composed with the
trusted `WriteAt`, nothing observable is lost:
- Go retries the rest. If the retry succeeds, the result is `(len, nil)`, which the model gives in
  one step.
- If the retry fails, the result is `(0, err)` with a prefix landed, which the model gives as
  `(k, e ≠ 0)`.
- Between the two calls, the model treats the rest of the range as still in flight, which is stuck or
  arbitrary for observers, not more defined.

So this is not unsound for Go programs, only less faithful at the step's own level. Allowing
`(k, 0)` with `0 < k < len` costs nothing, because the trusted loop already retries (`os.lean`,
`File.WriteAt.impl`, the final `else "pwrite" "nn"`).

## Accepted assumptions, recorded

- **No mixed writeback** (`:23-25`). Neither ext4 nor xfs promises it: without stable pages, a page
  under DMA can be changed by a concurrent `pwrite` or a store through a mapping. It is stated as an
  assumption, as it should be. It is the one assumption here that ordinary hardware does not justify;
  it should stay visible in the adequacy statement.
- **Another process's `fsync` of a file in the roots' trees** consumes the file's writeback error
  (`errseq`'s `SEEN` bit), so the program's own `fsync` returns 0 after a lost writeback. The header
  forbids other processes *changing* the trees, not syncing their files. F1's assumption makes this
  moot; without it, add "no other process opens a file in the roots' trees".

## Attacks the model survived

The directory tree and the journal:
- **The crash keeps a prefix of `metaLog`** (`MachineCrash`, `:737-738`). jbd2 and the xfs CIL
  commit transactions in order, and each syscall's changes are one transaction. `MetaBegin`
  (`:597-598`) makes the model's order the kernel's order, because no two metadata calls overlap.
  More committed than the model knows is covered: any prefix.
- **`dirCommitLen` (`Tree.lean:85-104`).** v6.12 ext4 commits the whole journal on a directory
  `fsync` (`ext4_fsync_journal`: `!S_ISREG` → `ext4_force_commit`). xfs forces the log up to the
  directory inode's last commit sequence, and every create, remove, mkdir and rename logs the parent
  (or parents) of its paths. The rebinding test makes the path identify the fd's directory: the
  operations that could move or replace that directory while the fd is open are stuck (`Rename`,
  `:641-642`; `Rmdir`, `:659`), and those before the open zero the commit. A failed directory
  `fsync` commits any `n ≤ dirCommitLen` chosen demonically, which includes 0.
- **A file `fsync` commits no name** (`:552-560`). This is weaker than ext4 (whose commit, via
  `ext4_sync_parent`, covers more) and than xfs: sound.
- **`fdatasync` treated as `fsync`.** Checked for the size: ext4's `ext4_do_update_inode` sets
  `i_datasync_tid` whenever `i_disksize` changes (`need_datasync`, `inode.c:5109-5149`), so
  `fdatasync` persists a shrink or a growth. xfs's datasync skips only timestamp-only changes.
- **Rename, unlink, rmdir and mkdir.** Every Linux errno case (`EISDIR`, `ENOTDIR`, `ENOTEMPTY`,
  `EINVAL` into its own tree, `ENOENT`, `EEXIST`) falls into the any-errno branch. Each success
  branch has a failure twin with or without the effect. `rename(a, a)` is a no-op success or any
  errno. `RenameOk` (`:436-441`) checked against t an ancestor of s, a file onto a directory, a
  directory onto a file, and a non-empty target.
- **`MetaOp.apply`/`moveTree`/`rekey`.** Replaying a prefix reproduces exactly the intermediate
  trees, because operations are checked against `replay metaLog treeDur` (`OsState.tree`) and logged
  in order. `DirSync`'s `metaCommit` folds a prefix without reordering.
- **Tree shape is preserved** (no hard link from a replay; parents exist). The steps keep
  `TreeShape`: renames replace or move whole subtrees, rmdir needs an empty directory, and creates
  and mkdirs need `ParentDir`.
- **Inodes.** Every inode the tree or the log names is in `files`: creates add it before logging,
  nothing removes it before a crash, and after a crash `files` holds exactly the inodes the crashed
  tree names, with an empty log. So a crash's replayed prefix never names a missing file
  (`MachineCrash`'s `∃ f`), and `OpenEffect`'s `i ∉ files` (`:427`) never makes a step impossible.
  Unlinked-but-open files stay until a crash, so the case "create `a`, unlink `a`, crash keeping only
  the create" finds the file (jbd2 does not reuse freed blocks before the freeing transaction
  commits, so its data is intact). A process restart keeps them, which is sound: inode numbers are
  internal.
- **Readdir** (`DirReadNext`, `:615-627`).
  - I tried ext4 returning an untouched name twice through a linear-to-htree conversion. `is_dx_dir`
    (`dir.c:45-55`) already treats a one-block directory as htree, and conversion happens only from
    one block, so the hash-order read never switches mode.
  - `ext4_dx_readdir` refills from the next unreturned hash after a change (`dir.c:555-634`). An
    untouched name is returned exactly once, short of a 62-bit hash collision split across a refill
    (not tried further).
  - Names removed or renamed meanwhile may be returned, and a touched name again (the round-1
    repair). The end needs only the untouched, still-present names, and the first call begins the
    read, as `getdents` does.
- **`Open`'s cases** (`OpenEffect`, `:420-427`). `O_CREAT` and `O_TRUNC` on a directory, `O_TRUNC`
  with `O_RDONLY` (Linux truncates), a missing parent, and a component that is a file all fall into
  the failure branch or behave as Linux does. A failure after the create or the truncate is covered.
- **`LstatDir` with `os.Rename`** (`:632-634`). Every Go outcome for a directory target (`EEXIST`, or
  `lstat(old)`'s error) is a nonzero errno the model can return, and `(0, _)` covers a failed
  `lstat`.

Data and sizes:
- **Crash sizes** (`CrashImage`, `:724-728`). Delayed allocation's intermediate `i_disksize`, xfs's
  size before data (zeros: every sector's version list contains the zero version it started from),
  and a shrink's orphan-list completion (the size changes first, then blocks are freed) all lie in
  `[sizeLo, sizeHi]`, widened by an in-flight change's target.
- **Sector versions against page writeback.** Writeback writes whole pages or blocks, but the
  sectors it did not change are rewritten with the same bytes. Per-sector independent choices
  (each sector its own `∃ v` and its own `Landed`, `:729-730`) cover writeback reaching the
  pages of one write out of order (page 1 old, page 2 new).
- **Several in-flight writes in one sector.** `Landed` over any permutation with a prefix of each
  covers every order `i_rwsem` serializes them in. The same holds when an `O_TRUNC` open makes two
  disjoint in-flight writes overlap.
- **Truncate and crash.** A shrink's cut sectors get a zero version, so an old size with old data
  and a new size with zeros are both reachable, and an in-flight shrink's target widens the range.
- **`fsync` with changes in flight.** Busy sectors keep their dirty bit and versions; the sizes
  collapse to the current size, and the in-flight target keeps the rest reachable.
- **A failed `fsync` after a partly successful writeback.** Some pages really were written, and the
  model keeps them lost (more outcomes). The sizes are unchanged, so a commit of the size or no
  commit are both covered. `errseq` reporting the error again on another fd is covered too, because
  `fsync` may always fail. (What fails is F1, the other direction.)
- **`EINTR` excluded from `fsync`.** ext4's and xfs's waits there are uninterruptible.
- **Races through `O_TRUNC`** (which, unlike `ftruncate`, does not check `BusyAt`). Each Linux
  order of a truncating open against an in-flight `pwrite` or `fallocate` is a placement of the
  model's steps, because the write lands at `…Finish` and that step can be put where the kernel
  landed it (the inode lock serializes them). The extra `fallocate` size is known (review round
  2): sound.
- **`pread` and `fstat` racing changes.** `filemap_read`'s per-batch `i_size` gives a length
  between the sizes, which `StatSees` allows, and the bytes under a change are arbitrary.
- **A process restart.** The page cache, the dirty bits and the metadata log survive, as the
  kernel's do. A metadata call in flight (`metaBusy`) has or has not happened, since the crash can
  be placed before or after its atomic step. The journal goes on committing in the same order after
  a process death: orphan cleanup of the dead process's unlinked files adds later transactions.
- **`close`, `flock` and OFD locks**: any errno. Freeing the fd always matches Linux, and the lock
  steps give no guarantee a proof could misuse.

## Stuck or less defined than Linux (sound; the clients hit some of these)

- **`MetaBegin` (`:597-598`).** Two metadata calls cannot overlap. etcd's WAL does exactly that: the
  `filePipeline` goroutine creates `N.tmp` while `cut` renames, and the purge goroutine removes old
  segments beside both. This is round 1's item 4 and still the main obstacle to verifying the WAL.
- **Rename or rmdir with a directory fd open on the target, or in the moved tree.** Linux allows
  both. etcd keeps `w.dirFile` open on the WAL directory for the WAL's life (renames inside it are
  fine). Whether `wal.Create`'s rename of the `.tmp` directory happens with a directory fd open
  below it was not checked.
- **`dirCommitLen` is 0 for a directory just made or moved,** where ext4 and xfs commit its
  creation. `wal.Create` fsyncs the parent after renaming the directory, which commits nothing in
  the model.
- **Overlapping in-flight writes** are stuck (two appends at once). bbolt has one writer, so it is
  unaffected.
- **Mapped loads past EOF** are stuck; Linux reads zeros up to the end of the page. bbolt maps past
  the file's size, but reads only pages inside it.
- **A second `Readdirnames`** on one fd; `Readdirnames(n > 0)`; `Fstat` of a directory fd;
  metadata calls on a root; unsupported open flags (`O_APPEND`, `O_EXCL`, `O_SYNC`). None of these
  is on etcd's or bbolt's paths as far as checked: `fileutil` opens with
  `O_WRONLY|O_CREATE[|O_TRUNC]` or `O_RDWR`, and bbolt opens with `O_RDWR|O_CREATE`.

## Not tried

- No crash test of the other findings (dm-log-writes, CrashMonkey); F3 was settled by one
  (`fs-v2-f3/f3.sh`).
- No search for an inconsistency in the Lean definitions (`⊢ False` from `OsCrash`, `FsInit`).
- xfs internals beyond `fallocate` and the zeroing on extension: reflink copy-on-write
  overwrites, shortform/block/leaf directory conversions during readdir (offsets are designed to be
  stable; not read).
- ext4 `data=journal`'s writeback-error path, inline data, encryption, casefold (excluded by the
  header), quotas (`EDQUOT` at writeback would be F1's case), DAX.
- The interplay of `HeapRendered` with Perennial's non-atomic cell modes during a concurrent Go load.

## Disposition (2026-11-05, by the author of the semantics)

F1 and F2: environment assumptions, worded as proposed (`Impl.lean`'s header, "No failed
writeback", "Durable at first start"). F3: the proposed model change (`CrashFile` keeps whole
sectors; `OsFile.resized`/`written` fill from `rawAt`), reverted on 2026-11-08 when a crash test
refuted F3 (see F3). F4, F5, F6: the proposed model changes
(`PRead`'s short success, `Landed.trunc` to any size between, `PWriteFinish`'s short success). The
stuck cases are recorded in `notes/fs-semantics-v2.md`, "After the soundness audit", for a decision
before the WAL's proof.
