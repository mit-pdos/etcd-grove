# Review, round 5: the trusted base of branch `fs-v2` on configuration C

**Date:** 2026-11-10. **Reviewed:** branch `fs-v2` at `39c5b3c91c` (merge base `1fbbd2504b` with
`origin/lean`), on configuration C (`fs-config/README.md`; every experiment below made its
filesystem with `fs-config/mkfs-mount.sh` and passed `fs-config/check.sh`). In scope, as round 4:
the top-level statements (`bboltfs/Results.lean`'s `bootCrashSafety` over `BootNoTear.lean`,
`crashlog/Results.lean`, `walfs/{Results,SegLogResults,DirSwapResults}.lean`) and the Go programs
they are about; the semantics `GooseLang/Ext/Fs/{Impl,Tree,Paths,Lookup,FilteredSem,AdequacyS,
NoTear}.lean`; the models `TrustedCode/{os,syscall}.lean`, `TrustedCode/golang_org/x/sys/unix.lean`
(changed since round 4 only by M1's fix); `etc/goose.py`'s project `walfs` (unchanged). Rounds 1-4
were read first, their dispositions checked rather than assumed.

**Method.** The `axiom` skill's, for a trusted semantics: a finding is a real run on C (a Go
program, an interleaving, a crash point) whose outcome the model or a stated premise excludes, or a
rule a proof can use that C does not honour. This round targets the three open items the brief
names, each with a new measurement method on C:

- (a) NoTear's "source buffer present" assumption: a Go program, with a `bpftrace` probe on ext4's
  `write_end` counting short copies and where each cut lands in the file page;
- (b) the journal order of metadata calls: `dm-log-writes` under the C filesystem, the disk rebuilt
  at every flush/FUA point of the log, recovered, and checked against `Follows`/`Closed`/`DirSync`;
- (c) durable zeros: `dm-log-writes` again, the disk rebuilt after *every* logged write, recovered
  by the kernel (mount: journal replay and orphan cleanup), checked against `CrashFile` and then
  extended to expose any written block left past the size; and extensions past the end block over
  a crash-made stale tail.

Kernel claims were read in the v7.0 sources round 4 fetched (`.lake/review-r4/k`) and
`drivers/md/dm-log-writes.c` (v7.0). The scripts are in `fs-v2-r5/` beside this report; no Lean
counterexample was built (report only, as the brief asks).

## Verdict

**No run on C found whose outcome a top-level theorem excludes.** The metadata journal order (b)
and the durable-zeros rule (c), both argued until now, were measured in the clients' exact cases
and held at every crash point (0 violations in 13 scenarios, 653 crash images). One stated
assumption is false on C (A1): the source buffer of a `pwrite` is *not* reliably present, both for
Go memory the program did not write (every time) and for memory it did write (memory compaction:
measured); minibolt's runs still satisfy the premise, but for a reason the premise does not state
(its buffers are page-aligned), and its docstring's "minibolt fills its pages" is false. The rest
are simplifications (two special cases no proof uses) and documentation.

| # | severity | finding | evidence |
|---|---|---|---|
| A1 | too-strong assumption (`NoTearCrash`, premise of `bootCrashSafety`; minibolt still meets the premise, by alignment) | the "source present" assumption is false on C: fresh Go heap pages are never present (1000/1000 writes committed a 1948-byte mid-page prefix); program-written pages go absent under compaction (5 mid-page commits in 3·10⁶ writes); "minibolt fills its pages" is false (`init`'s `first`) | **tested on C** (`notear/`), kernel and Go source |
| B1 | (no finding) journal order measured | `Follows`/`Closed`/`DirSync` held at every flush/FUA point: segdir, dirswap, crashlog, replace, overlapping calls in two directories, cross-directory renames | **tested on C** (`meta/`) |
| C1 | (no finding) durable zeros measured | `CrashFile`/`ofDisk`/`synced` held after every logged write in 7 scenarios (truncate racing writeback, shrink, `fallocate` 0 and `KEEP_SIZE`, a gap write, seglog's exact calls, minibolt's grow-and-sync); every extension of every recovered file read zeros; extensions past the end block over a stale tail read zeros | **tested on C** (`data/`) |
| S1 | simplification | `Follows`' lock and cross-rename clauses (`MetaOp.locks`, `MetaOp.crossRename`) are used by no proof: every client's log is `Sequential` and `Crash.lean` uses only `y < ex.start` | read (grep) |
| S2 | simplification (and doc mismatch) | `DirSync` commits only `Needed (lastTouch …)`, through `MetaOp.dirs`; the header says, and ext4 does (`ext4_force_commit` for a non-regular file), "commits the whole journal": one rule, two fewer definitions | kernel source; measured in B1 |
| S3 | simplification | NoTear's premise justified by alignment instead of a machine property: the cut is at a file page boundary whenever the buffer address ≡ offset (mod 4096), which Go's size classes give minibolt | Go source, A1's `aligned` runs |
| D1 | doc-only | `NoTear.lean:41-52`, `semantics/notear.go`: "minibolt fills its pages", "a program meets the first by writing every page", the list of absence causes; `crash.sh`/`f3.sh` recover with `e2fsck -fy`, not the kernel's replay | read; C1 used kernel recovery and agrees |

The table at the end repeats this with the fixes.

## Findings

### A1 (too-strong assumption): a pwrite's source is not "present while the call runs" on C

**The claim.** `NoTear.lean:41-52`: "**Assumed: the source buffer is present while the call
runs.** … A source page is not present if the program never wrote it (Go memory fresh from the OS
is not touched by Go), if it was swapped out (C has no swap), or while the kernel migrates it
(compaction, `khugepaged`, NUMA balancing): the premise assumes none of these happens during a
`pwrite`. A program meets the first by writing every page of the buffer before the call (minibolt
fills its pages); the last is a property of the machine … and is assumed." It is the justification
of `NoTearCrash` (a write in flight is cut only at a page cut), which `bootCrashSafety` takes as a
premise on the executions (`BootNoTear.lean:37`, `fsExtsSemanticsWithS NoTearStep NoTearCrash`).

**What C does.** `generic_perform_write` (`mm/filemap.c:4296-4386`) copies with faults disabled
and no prefault; a copy that meets an absent source page stops there, and `ext4_da_write_end`
commits the copied prefix of an uptodate folio and unlocks it before the source is faulted in
(round 4, N1, measured with `userfaultfd`). This round measures *when* the source is absent on C,
without `userfaultfd`: `notear/main.go` writes 4096 bytes at file offset 0 (an 8192-byte file,
synced and cached) from a buffer that starts 2148 bytes into a page; `notear/notear.bt` counts
`ext4_da_write_end` calls with `copied < len`, keyed by `(pos + copied) % 4096` (where the committed
prefix ends in the file page) and `copied`:

| mode (`notear/run.sh`) | writes | short copies `(cut in page, copied)` |
|---|---|---|
| `fresh`: each buffer a new `make([]byte, 1<<20)`, the program writes its first 4096 bytes only | 1000 | `[1948, 1948]` ×1000, `[1948, 0]` ×1000: **every write committed a 1948-byte mid-page prefix** |
| `all`: one 64 MiB buffer, every byte written by the program first; `COMPACT=1` (a loop writing `/proc/sys/vm/compact_memory`) | 3·10⁶ | `[1948, 1948]` ×5, `[1948, 0]` ×4: **mid-page commits of program-written memory** |
| `all`, no compaction loop | 3·10⁶ | none |
| `aligned` (buffer on a page boundary, as minibolt's), `COMPACT=1` | 3·10⁶ | none (a short copy would cut at 0, a page cut) |

So both of the assumption's halves are false on C. (i) Go does not zero memory fresh from the OS
(or returned to it: the scavenger's `MADV_DONTNEED`, `runtime/mem_linux.go`, after which Go knows
it is zero), so a buffer page the program did not write is absent, every time. (ii) A page the
program did write is absent while compaction migrates it (its PTE is a migration entry, and the
atomic copy does not wait for it); compaction is part of C (kcompactd, proactive compaction at the
default `vm.compaction_proactiveness = 20`, direct compaction for any high-order allocation on the
machine); the loop only makes it frequent. `khugepaged` and NUMA balancing do not touch a Go heap
on C (THP `madvise`, and Go 1.27 madvises `MADV_HUGEPAGE` only its metadata,
`runtime/malloc.go:869,960`, `mpagealloc.go:420,479`; one NUMA node, `numa_balancing = 0`): reasoned
from the source, not measured. The committed mid-page prefix is what round 4's N1 showed a
concurrent `fsync` or the flusher can write and a crash keep.

**minibolt.** "minibolt fills its pages" is false: `DB.init` writes `first :=
make([]byte, 4*pageSize)` with only pages 2-3 copied into it (`minibolt.go:128-130`); pages 0-1 are
never written. The premise still holds of minibolt's runs, for another reason: every buffer it
writes is a `make([]byte, 4096)` or `make([]byte, 16384)` (size classes 44 and 59 of go1.27.3,
`internal/runtime/gc/sizeclasses.go:50,65`, object alignment 4096 and 8192), at a page-multiple
offset, so every source page boundary is a file page boundary and any short copy cuts at a page
cut (the `aligned` row). So `bootCrashSafety` is not refuted and not vacuous on minibolt's real
runs; but its premise is justified by an assumption false on C, and true of minibolt by an
argument it does not state. A future client that writes a slice at an offset not congruent to its
address (a record appended to a WAL from an unaligned buffer, `buf[n:]`) would violate the premise
on C, and the theorem would silently not cover its runs.

**Fix (S3).** State the premise's justification as what C does: a write in flight is cut at a file
page boundary or where its *source* crosses a page boundary. For the premise as written, the
environment assumption becomes "each `pwrite`'s buffer address ≡ its offset (mod 4096)", a
property of the program (Go's size classes for minibolt), not of the machine; or restrict
`NoTearStep`/`NoTearCrash` to writes whose source and file pages coincide, passing `addr % 4096`
from the trusted `WriteAt` model (round 4's option (a)). Either way, drop the "present" assumption
and "minibolt fills its pages".

### B1 (measured, no finding): the journal order of metadata calls on C

**The claims.** `Tree.lean` (`Follows`, `Closed`, `Needed`) and `Impl.lean`'s header ("The journal
commits whole transactions, in order; a metadata call joins a transaction no earlier than those of
the calls that returned before it began …; an `fsync` of a directory commits the whole journal"),
argued in rounds 1-3, never measured.

**Method.** `meta/meta.sh` makes a C filesystem, sets up the starting state (synced), puts
`dm-log-writes` (v7.0) under it, mounts it with C's options plus `commit=1`, and runs one scenario
of `meta/metaops.go` (the clients' exact sequences; a 2.5 s pause between calls so that each lands
in its own transaction; each call's begin and end times recorded, and a log mark after each
returned call). `meta/replay.py` replays the log onto the base image and stops at every flush or
FUA entry (the commit blocks, and every point a device that honours flushes can be at),
recovers the image (`e2fsck -fy`, as `crash.sh` does: for names only, which D1's caveat does not touch), mounts it read-only, and checks the tree:

| scenario (the client) | crash points | distinct images | violations |
|---|---|---|---|
| `segdir` (walfs `Boot` from a leftover: unlink `seg.tmp`, create, write, fdatasync, rename to `seg`, fsync dir) | 28 | 5: old `seg.tmp`; none; empty `seg.tmp`; `seg.tmp` with data; `seg` with data | 0 |
| `dirswap` (walfs `Create`: mkdir `wal.tmp`, create `wal.tmp/seg`, write, fsync, rename the directory to `wal`, fsync dir) | 26 | 5, every one a prefix; `wal` always with `seg` and its data | 0 |
| `crashlog` (create, write 8, fdatasync, write flag, fdatasync) | 23 | 5, incl. size 9 with the flag `00` (allowed: the end page's first version) | 0 |
| `replace` (create `tmp`, write, fsync, rename over a synced `target`, fsync dir) | 26 | 3: old; old + `tmp`; new | 0 |
| `overlap` (two threads: create+rename 400 files each in `a/` and in `b/`, no sync, 10 ms apart) | 30 | 6 | 0 |
| `xrename` (two threads: 400 cross-directory renames each, `a/` and `b/` into `c/`) | 30 | 6 | 0 |

Checked per image: each directory's kept calls are a prefix of that directory's calls; across
directories, a kept call keeps every call that returned before it began (`Follows`' `y < ex.start`,
by the clock); the clients' invariants (`seg` ⇒ data; `wal` ⇒ `wal/seg` with data; flag ⇒ data;
`target` old or new, never both names new); and after the mark of a returned directory fsync, the
final state (`DirSync`). The kernel source agrees: `ext4_create`/`ext4_rename`/`ext4_unlink` start
their handle before the change becomes visible (`d_instantiate_new` inside the handle, `d_move`
after it), so a call that took effect before another began is in an earlier or the same
transaction; `ext4_sync_file` on a directory is `ext4_force_commit` (`fs/ext4/fsync.c:120-121`).

**Limits.** The replay takes the writes in completion order and cuts only at flushes; a device
that reorders writes between flushes gives more states (jbd2 is designed for them; not explored).
The cross-directory case cannot discriminate `crossRename` (the effect order of overlapping renames
is not observable), and the `overlap` images are few (two to five commits per run). xfs is outside
C.

### C1 (measured, no finding): durable zeros on C

**The claims.** `Impl.lean`: `diskSec`, `OsFile.ofDisk` (a crash image: the pages wholly past the
size zeros, the end page as on disk), `OsFile.synced` (after a successful sync, the non-busy
sectors of pages past the size are zeros and only zeros), `CrashFile` (a size since the last sync,
each sector one of its versions since then), `FallocKeep` (no change), and the header's "an
extension reads zeros past the old size, stale bytes included".

**Method 1 (`data/data.sh`, `data/dreplay.py`).** A C filesystem under `dm-log-writes`; one
scenario of `xfs_io` calls from a synced file (log marks after each sync that returned); the log
replayed with a stop after *every* logged write (each prefix in completion order), each image
recovered as a boot does it (mount: the kernel's journal replay and orphan cleanup, no `e2fsck`);
the file `f` checked against the model (size in the range since the last sync passed; every
512-byte sector within the size equal to one of the file's states since that sync); then the file
extended to 128 KiB and every byte past its old size checked zero (which would expose a written
block left past the size, the case durable zeros excludes):

| scenario | crash points | images seen | violations |
|---|---|---|---|
| `trunc-race`: 8192 `a`; `b` over page 1, its writeback started, `ftruncate 100` at once | 51 | 8192 `a`; 8192 `a`/`b`; 8192 with page 0's tail zeroed and page 1 `b`; 100 | 0 |
| `shrink`: 8192 `a`; `ftruncate 100` | 50 | 8192; 8192 with the tail zeroed; 100 | 0 |
| `falloc0`: 4096 `a`; `fallocate(0, 0, 16384)` | 47 | 4096; 16384 with zeros | 0 |
| `keep-past`: 100 `a`; `fallocate(KEEP_SIZE, 0, 16384)`, fsync; `b` at 8192 | 60 | 100; 8193 with zeros and `b` | 0 |
| `gap`: 100 `a`; `b`×10 at 5000 | 53 | 100; 5010 | 0 |
| `seglog`: seglog's `Segment` and `ZeroToEnd` calls exactly | 57 | 0; 65536 with the data and zeros | 0 |
| `grow-sync`: 16384 `a` (minibolt's four pages); `ftruncate 32768`, fsync; page 4 `b`, fdatasync; page 0 `c` | 61 | 4, each allowed in its sync epoch | 0 |

**Method 2 (`data/ext.sh`).** round 1's F3 stale tail (a synced one-byte file `00`, `07` written
back at 1 with the size not committed, the image copied; recovered by the kernel: size 1, block `00
07`), then an extension *past the end block*, which `f3.sh` did not try (it extended to 4 bytes):
`ftruncate 8192`, `pwrite` at 5000, `pwrite` at 4095, `fallocate(0, 0, 8192)`, `fallocate(0, 4096,
4096)`, `fallocate(KEEP_SIZE, 0, 8192)` then `pwrite` at 5000. Every one read `00 00 00 00` at bytes
0-3, before and after `sync` and `drop_caches`.

The durable-zeros rule therefore held in every case the brief lists (shrink then crash, truncate
down racing writeback, writes past the end, `fallocate` 0 and `KEEP_SIZE`) and in seglog's and
minibolt's exact sequences. As in B1, the replay is in completion order; the dioread_nolock race
(a commit before the data write completes) needs `fs-config/crash.sh`'s `dm-delay` and was
measured there in round 4 and the C README.

### S1 (simplification): `Follows`' lock and cross-rename clauses are used by no proof

`Follows` (`Tree.lean:132`) has three disjuncts: `y < ex.start`; a common directory in
`MetaOp.locks` (`:98`); both renames across directories (`MetaOp.crossRename`, `:105`). The only
lemma any proof uses about the crash's kept set is `Crash.lean`'s: in a `Sequential` log (every
call began after the previous one took effect: all of walfs's, crashlog's and minibolt's metadata
calls are on one thread) a closed set is a prefix, from the first disjunct alone (`follows_seq`).
The other two are referenced only by `Tree.lean` and `Tests.lean`. Dropping them only weakens the
model (more crashes allowed), so it stays sound, and removes two definitions and the header's
`i_rwsem`/rename-lock sentence from the trust base. They were measured (B1's `overlap`, `xrename`:
held), so keeping them is also defensible for a future concurrent client; if kept, the tree
invariant after a crash of a concurrent log (no cycle, each node named once) is what they would be
for, and no lemma proves it today.

### S2 (simplification, doc mismatch): `DirSync` commits through `lastTouch`, the header says the whole journal

`DirSync` (`Impl.lean:709`) commits `Needed log (lastTouch log df.ino)` (through `MetaOp.dirs`,
`Tree.lean:88,152`, and `commitThrough`, `Impl.lean:503`); the header (`Impl.lean:29`) says "an
`fsync` of a directory commits the whole journal", and so does ext4 on C: `ext4_fsync_journal` calls
`ext4_force_commit` for any non-regular file (`fs/ext4/fsync.c:120-121`), committing the running
transaction, which holds every call that took effect before it (B1: the handle starts before the
change is visible). The rule "a successful `DirSync` commits every logged entry" is sound, is what
the header says, and removes `lastTouch` and `MetaOp.dirs` (the walfs proofs fsync the directory
whose rename is the last entry, so the change to `TreeSpecsDirFd.lean:265` is local). (`MetaOp.dirs`
also differs from `locks` only by a moved directory, a case no client fsyncs.)

### D1 (doc-only)

- `NoTear.lean:41-52` and `examples/osfs/semantics/notear.go`: "minibolt fills its pages" (false,
  `minibolt.go:128`), "a program meets the first by writing every page", and the claim that
  migration during a call is a machine property "assumed" not to happen (it happens on C, A1);
  replace with the alignment argument (S3).
- `fs-config/crash.sh` (`:44,87`) and `fs-v2-f3/f3.sh` recover a crash image with `e2fsck -fy`; a
  boot recovers with the kernel's journal replay (or `e2fsck -p`), and a forced full check can
  change what the kernel would keep (it fixes `i_size` against initialized blocks past it). The
  cases measured here agree under kernel recovery (`dreplay.py`), but the helper should recover the
  way a boot does (mount, or `e2fsck -p`) so that its results mean what they say.

## Attacks that failed

- **Journal order, durable zeros**: B1, C1 above.
- **`fdatasync` and sizes**: the model treats `fsync` and `fdatasync` alike. On C a change of
  `i_disksize` sets `i_datasync_tid` (`ext4_do_update_inode`, `fs/ext4/inode.c:5591-5592,5630`), so
  `fdatasync` commits size changes, truncate-up and `fallocate` included (C1's `seglog`,
  `grow-sync`).
- **`synced`'s linearization**: a successful `fsync` is placed at its scan's start; writes finished
  before it are dirty then and written and waited for (`WB_SYNC_ALL` waits for writeback already in
  flight and rewrites); writes in flight are `busy` and untouched; the sizes of writes finished
  before it are committed through `i_datasync_tid`. No run found where the collapsed version is not
  on disk.
- **Crash sizes**: `i_disksize` moves only to sizes `i_size` had (writeback raises it up to
  `i_size`, truncate sets it), so it stays in `[sizeLo, sizeHi]` or an in-flight target; every image
  of C1 agreed.
- **The no-tear filter is still not vacuous** after the durable-zeros change: the crash keeping
  everything (each sector's last version, the current size) satisfies `NoTearCrash` with `k = 0`,
  since a sector of a page wholly past the size has `zeroSec` as its last version (it is so at boot,
  crash and sync, and every change that leaves a page wholly past the size writes zeros there).
- **No mixed writeback** (assumed): reachable on C only for a write into a page whose writeback is
  in flight; none of the clients writes a page twice without a completed sync in between (crashlog's
  flag after its `fdatasync`, minibolt's pages once per sync epoch, seglog's tail zeroing after its
  `fdatasync`), so no client run meets it.
- **`File.Write`'s M1 fix**: `ArbitraryInt` with the error and the offset unknown (-1): Go returns
  `nn ≥ 0` with the error (`poll.FD.Write`), covered; a later `Write`/`Read`/`SEEK_CUR` panics in the
  model, which the proofs avoid (seglog returns on the error).

## Not tried

- A Lean counterexample (none is due: no run found that a theorem excludes).
- Device reordering between flushes (B1, C1 replay in completion order); a torn sector (assumed
  atomic by C's device clause).
- `Readdirnames` under concurrent changes (ext4 htree split during a read returning an untouched
  name twice, which `DirReadNext` excludes); no client reads a directory while changing it.
- Go's scavenger: a page released with `MADV_DONTNEED` and reused is absent like a fresh one (A1's
  `fresh` mechanism); not measured separately.
- `O_TRUNC` (one step in `OpenEffect`, where `ftruncate` is two) racing a read or a mapping: no
  client opens with `O_TRUNC`.

## Summary

| # | severity | what | evidence | fix |
|---|---|---|---|---|
| A1 | too-strong assumption | NoTear's "source present" false on C (fresh heap: always; written memory: under compaction); "minibolt fills its pages" false; minibolt meets the premise by alignment only | tested on C (`notear/`); kernel, Go source | justify by buffer/offset congruence mod 4096 (S3), or restrict the premise to aligned writes |
| B1 | none (evidence upgrade) | journal order held in 6 scenarios, 163 crash points | tested on C (`meta/`) | — |
| C1 | none (evidence upgrade) | durable zeros held in 7 scenarios (379 crash points) and 6 extensions | tested on C (`data/`) | — |
| S1 | simplification | `Follows`' lock and cross-rename clauses unused by any proof | read | drop, or keep with a lemma that needs them |
| S2 | simplification (doc mismatch) | `DirSync` through `lastTouch`/`dirs`; header and ext4: the whole journal | kernel source; B1 | `DirSync` commits every logged entry |
| S3 | simplification | NoTear justified by a machine property rather than a program one | Go source; A1 `aligned` | state alignment |
| D1 | doc-only | NoTear docstring and `notear.go`; `crash.sh`/`f3.sh` recover with `e2fsck -fy` | read | reword; recover by mount |

## Scripts (`notes/axiom-review/fs-v2-r5/`)

All run as the user with `sudo` where they touch devices; each makes its filesystem with
`fs-config/mkfs-mount.sh` and refuses to run unless `fs-config/check.sh` passes.

- `notear/main.go`, `notear/notear.bt`, `notear/run.sh` (A1). Runs: `run.sh /tmp/r5a fresh 1000`;
  `COMPACT=1 run.sh /tmp/r5a all 3000000`; `run.sh /tmp/r5a all 3000000`;
  `COMPACT=1 run.sh /tmp/r5a aligned 3000000`. (`copy_folio_from_iter_atomic` and
  `fault_in_iov_iter_readable` are not traceable on this kernel, hence the probe on
  `ext4_da_write_end`, whose `copied < len` is exactly a short copy.)
- `meta/metaops.go`, `meta/meta.sh`, `meta/replay.py` (B1). Runs: `meta.sh /tmp/r5m SC commit=1
  2500` for `segdir`, `dirswap`, `crashlog`, `replace`; `meta.sh /tmp/r5m SC commit=1 10000` for
  `overlap`, `xrename` (the last argument: the pause, in ms, or µs for the threaded ones).
- `data/data.sh`, `data/dreplay.py`, `data/ext.sh` (C1). Runs: `data.sh /tmp/r5d SC` for each
  scenario of the table; `ext.sh /tmp/r5e EXT` for `trunc8192`, `write5000`, `write4095`,
  `falloc8192`, `falloc4096+4096`, `keep-write5000`.

Outputs (abridged):

```
mode fresh, 1000 writes:            @calls: 3001   @short[1948, 0]: 1000   @short[1948, 1948]: 1000
mode all, compaction loop, 3000000: @calls: 3000010  @short[1948, 0]: 4    @short[1948, 1948]: 5
mode all, 3000000 writes:           @calls: 3000001
mode aligned, compaction loop, 3000000 writes: @calls: 3000001

segdir: 28 crash points (flush/FUA entries), 5 distinct images, 0 violations
dirswap: 26 crash points (flush/FUA entries), 5 distinct images, 0 violations
crashlog: 23 crash points (flush/FUA entries), 5 distinct images, 0 violations
replace: 26 crash points (flush/FUA entries), 3 distinct images, 0 violations
overlap: 30 crash points (flush/FUA entries), 6 distinct images, 0 violations
xrename: 30 crash points (flush/FUA entries), 6 distinct images, 0 violations

trunc-race: 51 crash points (every logged write), 4 distinct images, 0 violations
  from entry 4 (after 0 syncs): size 8192, sectors: a* x1, 00 x7, b x8
shrink: 50 crash points (every logged write), 3 distinct images, 0 violations
falloc0: 47 crash points (every logged write), 2 distinct images, 0 violations
keep-past: 60 crash points (every logged write), 2 distinct images, 0 violations
gap: 53 crash points (every logged write), 2 distinct images, 0 violations
seglog: 57 crash points (every logged write), 2 distinct images, 0 violations
grow-sync: 61 crash points (every logged write), 4 distinct images, 0 violations

recovered: size 1, block 65536 on disk:  00 07 00 00
after write5000: size 5001, bytes 0-3:  00 00 00 00      (and likewise for the five others)
```
