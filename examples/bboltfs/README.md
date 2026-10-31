# bboltfs: Linux files, fsync and read-only mmap, as bbolt uses them

The acceptance tests for the file extension of `notes/osfs-ext-plan.md`
(`GooseLang/Ext/OsFs`). They are Go programs that call the operating system as
`go.etcd.io/bbolt` does (the fork's `bolt_unix.go`, `bolt_linux.go`, `db.go`,
`tx.go`, `mlock_unix.go`): `os.OpenFile`, `(*os.File).WriteAt/ReadAt/Stat/Truncate/Sync/Close/Fd/Name`,
`syscall.Fdatasync`, `syscall.Flock` and `unix.Mmap/Munmap/Madvise/Mlock/Munlock`, with bbolt's
flags. The OS calls stay at their call sites, so that a later step can move them onto the
wrapper package, whose signatures are the same.

The extension is enough for bbolt when:
- every target below is proved;
- minibolt's boot program is proved crash-safe under the premise below;
- no probe in `stuck/` can be proved (except `testCASMapped`, until the Perennial prerequisite
  lands);
- no probe in `twoways/` can be proved with `RET true` or with `RET false`.

`go test ./bboltfs/...` (from `examples/`, also under `-race`) checks the Go side:
- each target returns true on real Linux in a fresh `t.TempDir()`, without meeting an
  environmental failure;
- minibolt round-trips, and its boot program never panics when run again and again, or when
  killed at arbitrary points;
- the concurrent targets hold over 100 runs each;
- minibolt refuses every transaction after a failed commit;
- each stuck probe with a safe answer gives the answer recorded below;
- each probe that dies of a signal dies of that signal (in a re-executed child);
- each two-ways boot probe's phases run as designed, with a process kill standing in for the
  crash, and the racing two-ways probes run without a Go data race.

**Crashes cannot be tested in Go.** A killed process loses nothing, because the page cache
survives it. The crash properties, and the "false" answers of the two-ways probes, are claims
about the model's crash relation only. (`t.TempDir()` is on tmpfs here, while the model's
environment is ext4 or xfs. Nothing the tests check depends on the difference.)

Conventions. Each program takes the directory it works in, and opens only
`dir + "/" + name`. Its precondition says which of those paths are allowed (the model's
fixed path set) and that they are absent at the start. The model lets any operation fail with
an arbitrary errno and no effect. A target's claim is therefore about the runs where nothing
fails: on a failure it returns true through `envFailure`, which also counts the failure for the
Go tests. bbolt's `db.data`, a `(*[MaxMapSize]byte)` view of the mapping, is replaced by
indexing the mapped slice, as in Perennial's `unsafememory` patched forms. `page.go` holds
bbolt's `Page`/`Meta` layout and its FNV-64a `Sum64`, as in `unsafememory`.

## Targets (`targets.go`): each `{{ True }} testX(dir) {{ RET true }}`

| target | bbolt site | primitives | model rule | reasoning principle it forces |
|---|---|---|---|---|
| `testOpenCreate` | `Open`: `OpenFile(path, O_RDWR\|O_CREATE, mode)`, `db.path = file.Name()`, `Stat().Size() == 0` | Open (absent, without and with CREAT), Fstat, Close; `Fd`, `Name` | absent without CREAT is ENOENT; CREAT creates (`named := false`); Close frees the fd whatever its errno | a points-to for an absent path that Open turns into an fd token plus `path ↦ []`; the trusted `File`'s shared inner cell: after `Close`, `Fd()` is `^uintptr(0)` through a copy `g := *f` too |
| `testInit` | `db.init`: 4 pages, one `WriteAt` at 0, `fdatasync` | PWriteStart/Finish (extending an empty file), Fsync, Fstat | the affected range of an extending write; D3: fdatasync makes size durable | the extending write's effect on `cur` and on the dirty set; Fsync moves dirty bytes to the durable ghost state |
| `testReadPageSize` | `getPageSizeFromFirstMeta`, `getPageSizeFromSecondMeta` (page sizes from 1 KiB up, `bw == len(buf)` or `io.EOF && bw == fileSize-pos`) | PRead, Fstat | PRead returns `cur[off, min(off+n, size))` | reading a file's bytes back into a Go buffer and validating a meta there; a loop over candidate offsets, with a case split on what each holds |
| `testShortReadAt` | the `io.EOF` branch of `getPageSizeFromSecondMeta` | PRead across, at and past EOF | the `min(off+n, size)` cut; a short `ReadAt` is `io.EOF` | the trusted `ReadAt`'s short-read rule |
| `testMmapMeta` | `db.mmap`, `mmap(db, sz)`: 32 KiB mapping over a 16 KiB file, `Madvise(MADV_RANDOM)` with ENOSYS ignored; `db.page(0/1).Meta()`, `Validate`, `db.meta()`, `tx.init`'s copy; `munmap` | Mmap (longer than the file), Munmap | `render`: cells below EOF are `(Reading 1, byte)`, cells past EOF are holes | a points-to for phantom-reader cells (load-only); unsafe `Page`/`Meta` views and FNV over them; holes are never touched |
| `testWriteVisibleInMap` | `tx.write`'s pages, read by later transactions through `db.page` (no sync between); `NoGrowSync`'s extending write | PWrite under a live mapping | the one heap rule: every step re-renders the mapping, with no sync needed (MAP_SHARED coherence); an extending write turns the holes up to its end (and the zero gap) into cells | the per-byte file ghost state owns the mapped cells, so that a write's update of `cur` is its update of the mapping |
| `testGrowRemap` | `db.allocate`'s remap (Munmap, then Mmap at 64 KiB) before `db.grow`'s `Truncate` + `Sync` | Munmap, Mmap, FtruncateStart/Finish (extend), Fsync | Ftruncate zero-fills and marks dirty; the holes in the larger mapping become zero cells | giving the cells back at Munmap and getting fresh ones at Mmap; an extending Ftruncate under a mapping |
| `testOpenTrunc` | `CopyFile`: `O_RDWR\|O_CREATE\|O_TRUNC` | Open with TRUNC | TRUNC sets the size to 0 | TRUNC on an existing file |
| `testReadOnlyReopen` | `WriteTo`'s reopen (`O_RDONLY\|WriteFlag`, WriteFlag 0) and its SectionReader copy of pages 2 up to `tx.Size()` (which calls `ReadAt`); `Options.ReadOnly`'s O_RDONLY open, then mmap | Open RDONLY, PRead and Mmap on a read-only fd | fds are `(path, readable, writable)`; the state is per path | two fds share one file's state |
| `testFlock` | `flock` (`LOCK_NB\|LOCK_EX`, retried on `EWOULDBLOCK` with `time.Sleep`), `LOCK_SH` for a read-only open, `funlock` (`LOCK_UN`) | Flock | D7: nil or any errno; stuck on an fd not open | a retry loop whose exit is not guaranteed (partial correctness) |
| `testTrivialCalls` | `common.DefaultPageSize`; `mmap`'s `MAP_SHARED\|MmapFlags` with etcd's `MAP_POPULATE`; `Madvise`; `mlock`/`munlock` on `db.dataref[:sizeToLock]` | Mmap (POPULATE), Madvise, Mlock, Munlock, Getpagesize | the trivial calls; `Getpagesize` is 4096 | Mlock/Munlock accept a resliced mapping (unlike Munmap) |
| `testWriteAtEmpty` | (none: it pins down the model) | none: Go's `WriteAt` loops while bytes remain, so `WriteAt([]byte{}, 100)` makes no system call | a zero-length write changes nothing, even past EOF (`writeBytes`, and PWriteFinish with `k = 0`) | the trusted `WriteAt` with no bytes leaves the file as it was |
| `testConcurrentDisjoint` | `beginTx` (metalock, then `mmaplock.RLock`, copy the meta, unlock metalock) against `tx.write` + `tx.writeMeta` (free pages 4–7, fdatasync, then the meta for txid 2 in slot 0 under metalock, fdatasync) | concurrent loads, PWrite, Fsync | a mapped load is stuck only on a cell an in-flight change `Affects` | splitting the file's byte ghost state by range: the writer owns what it writes, readers hold read fractions of the pages their meta reaches, and metalock guards the meta slots; the invariant "pages reachable from a valid meta are not written" |
| `testWriteTo` | `tx.WriteTo` with `WriteFlag` 0 (etcd's snapshot): `beginTx`, the two generated meta pages, then pages 2 up to `tx.Size()` copied with `ReadAt` on `db.file`, while a writer reuses pages 5 and 6 (free in the reader's view) and commits txid 3 | concurrent PRead and PWrite, Fsync | `ReadSees`: a byte under an in-flight change is arbitrary, the rest are the file's, and the length is exact unless a change resizes the file (here none does) | the copy is claimed only on the pages the reader's meta reaches (its root and freelist), which the writer never writes: the same reachability invariant as `testConcurrentDisjoint`, now for a read through the file |
| `testStatRacingExtendBounded` | (`sameFile`'s and `db.fileSize`'s Stat, with `NoGrowSync`) | Fstat racing an extending PWrite | `StatSees`: between the size and the change's target (D8) | a bound that holds for every allowed answer; the exact answer is a two-ways probe |
| `testNegativeOffset` | (none: Go's own checks) | none (`ReadAt`/`WriteAt` return "negative offset" without a system call); `Truncate(-1)` is EINVAL | the trusted models return Go's error first; the primitives are stuck on a negative offset | the trusted models' argument checks |

## minibolt (`minibolt.go`)

minibolt is a two-meta-page store in bbolt's style, about 200 lines, holding one value:
- **Open:** OpenFile with O_RDWR|O_CREATE, then flock, Stat, init if the file is shorter
  than 4 pages, then mmap (32 KiB doubling, as `db.mmapSize`). It validates both metas
  (FNV-64a) and uses the valid one with the highest txid (`db.meta`, which panics when neither
  is valid). If neither is valid, it redoes init.
- **Commit(v):** under `rwlock`, it copies the meta under `metalock` and allocates page
  `pgid`. It remaps if the high water mark passes the mapping (`db.allocate`, under
  `mmaplock`), and grows the file to the mapping size if needed (`Truncate`, then `Sync`, as
  `db.grow`). It writes the data page and fdatasyncs (`tx.write`), then writes the meta to
  slot `txid % 2` under `metalock` and fdatasyncs (`tx.writeMeta`). If any step fails, the
  outcome is unknown, and the handle is marked failed: every later `Get` and `Commit` returns
  an error. This differs from bbolt (below).
- **Get:** a read transaction through the mapping (`metalock` and `mmaplock.RLock`, as
  `beginTx`).

**A failed sync (plan D2).** A failed `fdatasync` marks the bytes then dirty as *lost*. They
are clean, so no later sync writes them, and a crash makes them arbitrary until they are
written again and synced. minibolt handles each case as follows:
- **The data-page sync fails.** The lost bytes are the new data page, which no meta reaches. If
  the handle went on, a later commit at the same high water mark would rewrite and sync it, but
  minibolt stops instead.
- **The meta sync fails.** The meta slot is lost. A crash makes it arbitrary, and P1 below covers
  that. Until the crash, the page cache shows the new meta, so the commit is visible without
  being durable. bbolt's `writeMeta` returns the error and rolls back, but the new meta stays
  in the mapping. bbolt then serves it to new transactions and builds the next commit on it:
  a commit that reported an error can still become effectively durable. minibolt marks the
  handle failed, so it never reads or builds on such a commit. The boot program then stops,
  and the next boot (after a crash) decides from the disk.
- **The grow's Sync fails.** The size is not durable. No meta yet refers to the new pages, and
  the handle stops.

The boot check itself does not depend on the failed mark. Lost bytes are only ever bytes that
no durable meta reaches, or a meta slot, and P1 covers the slot. The mark is there so that
`Commit`'s error means "not done, as far as this handle is concerned".

**One deliberate difference from bbolt: init.** bbolt's `init` writes the metas and the
pages they point at (freelist 2, root 3) with one `WriteAt` and one `fdatasync`. A crash
before the sync completes may keep meta 0 and lose page 3. That is allowed by D1, and by Linux,
whose writeback order is arbitrary. The result is a valid meta over a garbage root, and bbolt
never recovers from it. minibolt writes and syncs pages 2–3 first, then the metas, and redoes
init when neither meta is valid. Under P1 that only happens before init's second sync
completed.

**The boot program `BootMinibolt(dir)`.** It is in the style of Perennial's
`goose/testdata/examples/crashfs`: it runs at every start and after every crash. Transaction
`t ≥ 2` stores the value `t`, and init's transactions 0 and 1 store none. Each boot opens the
database and checks three things:
- the current meta's root page holds that meta's value, or nothing for txid ≤ 1;
- after one commit, the commit is visible;
- `db.meta()`'s own panic does not fire.

On an error it stops. **The crash property:** none of these panics fires, however often the
node crashes. Page `t + 2` always holds value `t`, so a commit that a crash lost and the next
boot redoes rewrites the same bytes.

### The premise the proof needs

**P1: no checksum collision on a torn meta (plan D1).** A meta slot is the 64 bytes at
offset 16 of page 0 or 1. At a crash, take a slot some of whose bytes the crash relation makes
arbitrary: bytes that are dirty, lost by a failed sync, under an in-flight change, or at or past
the durable size. If the image's 64 bytes at that slot pass `Validate`, that is, `magic` and
`version` match and `checksum` is the FNV-64a of the first 56 bytes, then they equal either the
meta of the last `WriteAt` to that slot, or the slot's durable bytes. The rule does not ask
when that `WriteAt` happened: a lost slot stays arbitrary across later successful syncs.

This premise is needed under either D1 option: even with "old-or-written" bytes, a meta torn
between two metas could pass the checksum. There used to be a second premise, P2 ("no fsync
fails"). It is gone since D2 became precise (13578e6e19).

## Probes (`stuck/`): each `{{ True }} testX(dir) {{ RET true }}` must be unprovable

"Deliberately incomplete" means that Linux defines the result, but the model is stuck on
purpose. Every probe here except `testCASMapped` is less defined in the model than in Go,
which is sound.

| probe | Go/Linux | why the model is stuck |
|---|---|---|
| `testStoreMapped` | **SIGSEGV** (gc: "unexpected fault address", exit 2) | the phantom reader on every mapped cell makes every store stuck |
| `testLoadPastEOF` | **SIGBUS** (a mapped page wholly past EOF) | the cell is a hole |
| `testLoadPastEOFSamePage` | true (the EOF page's tail reads 0) | a hole: deliberately incomplete; bbolt's files are whole pages |
| `testLoadAfterMunmap` | **SIGSEGV** | Munmap removes the cells; this is the stale-page-after-remap bug that `tx.root.dereference` prevents |
| `testLoadAfterShrink` | **SIGBUS** | after a shrinking FtruncateFinish the cells past EOF are holes (and while it is in flight, every affected cell); bbolt only grows |
| `testLoadRacingWriteAt` | old, new or a mix (no fixed answer; not run) | the word is a hole while the write is in flight |
| `testMmapWritable` | true (allowed on O_RDWR; a store through it is seen by `ReadAt`) | prot must be `PROT_READ` |
| `testMmapOffset` | true (maps from page 1) | the offset must be 0 |
| `testMmapZeroLength` | true (EINVAL) | the length must be positive |
| `testMunmapResliced` | true (x/sys/unix: EINVAL for `b[:4096]` and `b[4096:]`; the mapping stays) | Munmap needs `len = cap` = the mapping's length, at its base |
| `testUseAfterClose` | true (`os.ErrClosed`, no system call) | the File's fd is -1: a closed fd |
| `testFdatasyncAfterClose` | true (`Fdatasync(-1)` is EBADF) | an fd not in the table |
| `testNeverOpenedFd` | true (`Flock(1<<20, LOCK_UN)` is EBADF) | a forged fd (D7) |
| `testOutsidePath` | true (`dir/../outside` is created) | the path is not allowed |
| `testAppend` | true (the open succeeds; `WriteAt` refuses O_APPEND) | O_APPEND is not an allowed flag |
| `testWriteReadOnly` | true (EBADF) | misuse: the fd is not writable (D6) |
| `testCASMapped` | **SIGSEGV** (amd64 `LOCK CMPXCHG` writes even when the compare fails; `code=0x2`, SEGV_ACCERR) | **not stuck today**: `CmpXchgBytesFailS` accepts cells with readers, so this probe is provable (unsound) until the plan's Perennial prerequisite lands |

## Probes (`twoways/`): neither `RET true` nor `RET false` may be provable

Two are racing programs: since D8 became nondeterministic (13578e6e19), a racing `pread` or
`fstat` returns any answer that `ReadSees` or `StatSees` allows, and the program asks for one
of them. The others are boot programs. A setup boot ends in `waitForCrash` (`for {}`), so only a crash
ends it, and only the observing boot returns. Each phase is kept in synced bytes of a file that
an earlier crash has already kept, so the answer depends only on what the last crash did to the
byte under test.

| probe | decision | true is possible because | false is possible because |
|---|---|---|---|
| `bootUnsyncedData` | D1 | the model makes the unsynced byte arbitrary, which includes the written value; Linux may have written the page back | arbitrary includes the old value; Linux may not have written it back |
| `bootUnsyncedName` | D4 | a file that survives a crash keeps its synced byte; ext4 and xfs in practice make a new file's name durable on its fsync | the file was created since boot and no directory was synced, so the crash may drop it; POSIX promises nothing |
| `bootFailedThenSync` | D2 | the first sync's failure made the payload *lost*; the second sync does not write it (it is clean), so the crash makes it arbitrary | the same; on Linux, the first sync's failure may have dropped the dirty page and marked it clean, and the second sync then has nothing to write |
| `bootUnsyncedTruncate` | size range | the size after the crash is anywhere in `[sizeLo, sizeHi]` = [1, 4096] | the same. Linux usually keeps the new size, because the phase file's fsync commits the journal, but nothing promises it |
| `testReadAtRacingWriteAt` | D8 (`ReadSees`) | without overlap the read sees one version, all old (1) or all new (9) | each byte under the in-flight write is arbitrary, so a mix is allowed; ext4 can return one |
| `testStatRacingExtend` | D8 (`StatSees`) | without overlap the size is the old (0) or the new (3 pages) one | any size between them is allowed; Linux's `generic_perform_write` moves `i_size` page by page. The bound itself is the target `testStatRacingExtendBounded` |

## Open points for the plan

The programs found these, in order of weight. Points 1–3, 5, 6 and most of 7 are resolved by
13578e6e19 (`OsFs: precise lost pages on a failed fsync (D2), nondeterministic racing
pread/fstat (D8)`), and point 4 is recorded as an issue.

1. **Resolved (13578e6e19): D2 made every crash property unprovable once a sync could
   fail.** Under poisoning, a crash after a failed sync made long-durable bytes arbitrary, so
   minibolt needed a premise "no fsync fails". D2 now marks only the bytes then dirty as lost,
   and P2 is gone.
2. **Resolved (13578e6e19): bbolt's `WriteTo` was stuck.** It copies pages that a concurrent
   writer may be rewriting. A racing `pread` now returns any mix (`ReadSees`), and the target
   `testWriteTo` claims the copy only on the pages the reader's meta reaches. With `WriteFlag`
   set (etcd may set O_DIRECT), the open is still stuck.
3. **Resolved (13578e6e19): PRead racing a shrinking Ftruncate was more defined than
   Linux.** Ftruncate is now two steps (`FtruncateStart`/`FtruncateFinish`). While it is in
   flight it affects every byte from `min(size, sz)` on, and a racing read's length is
   anything up to `n`.
4. **Recorded (`issues/bbolt-init-not-crash-safe.md`): bbolt's `init` is not crash-safe**
   (minibolt above). A proof of bbolt's crash safety needs the fork to sync pages 2–3 before
   the metas, or it must give up the property for a crash during init.
5. **Resolved (13578e6e19): a zero-length write past EOF.** `writeBytes` changes nothing when
   given no bytes, and PWriteFinish with `k = 0` leaves the file as it was. A partial write
   leaves size `off + k`. `testWriteAtEmpty` checks the first.
6. **Resolved (13578e6e19): negative offsets.** The trusted models return Go's error, and the
   primitives are stuck on a negative offset. `testNegativeOffset` is now a target.
7. **Smaller points.**
   - Resolved (13578e6e19):
     - `O_TRUNC` truncates whatever the access mode, and marks the file as `Ftruncate` does.
     - A file a crash keeps is named.
     - The environment assumptions add atomic sectors and no media errors.
   - Still open, and harmless: an environmental failure's errno is any nonzero one, so it
     includes ENOENT for an existing file. A program cannot use ENOENT to test existence (the
     two-ways probes use the size instead). bbolt branches only on EWOULDBLOCK and ENOSYS.
8. **Outside the file model, open:** the fork's `mmap` still sets
   `db.data = (*[common.MaxMapSize]byte)(unsafe.Pointer(&b[0]))`. That is the oversized
   array view that `unsafememory` replaces by `unsafe.Slice`, and it needs the same patch.
9. **New, bbolt (not the model): a commit that reported an error can become effectively
   durable.** After `writeMeta`'s fdatasync fails, the new meta stays in the page cache and so
   in the mapping. bbolt serves it to later transactions and builds on it (minibolt above).
   A spec of bbolt's `Commit` that reads an error as "not committed" is therefore false. Either
   the spec says "unknown", or the fork must stop using the handle after a failed sync, as etcd
   does by exiting.
