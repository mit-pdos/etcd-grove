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
- minibolt's boot program is proved crash-safe under the premises below;
- no probe in `stuck/` can be proved (except `testCASMapped`, until the Perennial prerequisite
  lands);
- no probe in `twoways/` can be proved with `RET true` or with `RET false`.

`go test ./bboltfs/...` (from `examples/`, also under `-race`) checks the Go side:
- each target returns true on real Linux in a fresh `t.TempDir()`, without meeting an
  environmental failure;
- minibolt round-trips, and its boot program never panics when run again and again, or when
  killed at arbitrary points;
- each stuck probe with a safe answer gives the answer recorded below;
- each probe that dies of a signal dies of that signal (in a re-executed child);
- each two-ways probe's phases run as designed, with a process kill standing in for the crash.

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
| `testGrowRemap` | `db.allocate`'s remap (Munmap, then Mmap at 64 KiB) before `db.grow`'s `Truncate` + `Sync` | Munmap, Mmap, Ftruncate (extend), Fsync | Ftruncate zero-fills and marks dirty; the holes in the larger mapping become zero cells | giving the cells back at Munmap and getting fresh ones at Mmap; an extending Ftruncate under a mapping |
| `testOpenTrunc` | `CopyFile`: `O_RDWR\|O_CREATE\|O_TRUNC` | Open with TRUNC | TRUNC sets the size to 0 | TRUNC on an existing file |
| `testReadOnlyReopen` | `WriteTo`'s reopen (`O_RDONLY\|WriteFlag`, WriteFlag 0) and its SectionReader copy of pages 2 up to `tx.Size()` (which calls `ReadAt`); `Options.ReadOnly`'s O_RDONLY open, then mmap | Open RDONLY, PRead and Mmap on a read-only fd | fds are `(path, readable, writable)`; the state is per path | two fds share one file's state |
| `testFlock` | `flock` (`LOCK_NB\|LOCK_EX`, retried on `EWOULDBLOCK` with `time.Sleep`), `LOCK_SH` for a read-only open, `funlock` (`LOCK_UN`) | Flock | D7: nil or any errno; stuck on an fd not open | a retry loop whose exit is not guaranteed (partial correctness) |
| `testTrivialCalls` | `common.DefaultPageSize`; `mmap`'s `MAP_SHARED\|MmapFlags` with etcd's `MAP_POPULATE`; `Madvise`; `mlock`/`munlock` on `db.dataref[:sizeToLock]` | Mmap (POPULATE), Madvise, Mlock, Munlock, Getpagesize | the trivial calls; `Getpagesize` is 4096 | Mlock/Munlock accept a resliced mapping (unlike Munmap) |
| `testWriteAtEmpty` | (none: it pins down the model) | none: Go's `WriteAt` loops while bytes remain, so `WriteAt([]byte{}, 100)` makes no system call | a zero-length write past EOF must not extend the file | the trusted `WriteAt` must not reach PWrite with no bytes (see the open points below) |
| `testConcurrentDisjoint` | `beginTx` (metalock, then `mmaplock.RLock`, copy the meta, unlock metalock) against `tx.write` + `tx.writeMeta` (free pages 4–7, fdatasync, then the meta for txid 2 in slot 0 under metalock, fdatasync) | concurrent loads, PWrite, Fsync | the only race rule: a load is stuck only inside an in-flight write's affected range | splitting the file's byte ghost state by range: the writer owns what it writes, readers hold read fractions of the pages their meta reaches, and metalock guards the meta slots; the invariant "pages reachable from a valid meta are not written" |

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
  slot `txid % 2` under `metalock` and fdatasyncs (`tx.writeMeta`).
- **Get:** a read transaction through the mapping (`metalock` and `mmaplock.RLock`, as
  `beginTx`).

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

### Premises the proof needs

**P1: no checksum collision on a torn meta (plan D1).** A meta slot is the 64 bytes at
offset 16 of page 0 or 1. At a crash, take a slot some of whose bytes the crash relation makes
arbitrary: bytes that are dirty, in an in-flight write, at or past the durable size, or in a
poisoned file. If the image's 64 bytes at that slot pass `Validate`, that is, `magic` and
`version` match and `checksum` is the FNV-64a of the first 56 bytes, then they equal either the
meta of the last `WriteAt` to that slot (begun or finished since the last successful sync), or
the slot's durable bytes. This premise is needed under either D1 option: even with
"old-or-written" bytes, a meta torn between two metas could pass the checksum.

**P2: no fsync fails (or D2 changes).** Under D2 as planned, a failed `Fdatasync`/`Sync`
poisons the file, and the next crash makes *every* byte and the size arbitrary, including
metas and root pages that have long been durable. The model allows the failure as an
environmental one. `Exit` is `AngelicExit`, and a crash still follows it, so no program can
protect itself. The boot program then reads a meta whose bytes are the old valid ones (which P1
allows) over a garbage root page, and its check fires. So the crash property holds only if no
fsync fails. The alternative is D2's other option, which bounds the loss: a failed sync loses
only the bytes then dirty, plus later writes it did not cover. With that option the property
holds as it does on Linux, because minibolt stops writing after a failure, and the lost pages
are unreachable (data pages) or covered by P1 (a meta). See the open points.

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
| `testLoadAfterShrink` | **SIGBUS** | a shrinking Ftruncate makes holes; bbolt only grows |
| `testLoadRacingWriteAt` | old, new or a mix (no fixed answer; not run) | the word is a hole while the write is in flight |
| `testReadAtRacingWriteAt` | old, new or a mix of pages on ext4 (not run) | PRead's range meets an in-flight write's affected range |
| `testStatRacingExtend` | old, new or an intermediate size (`generic_perform_write` moves `i_size` page by page; not run) | D8 |
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
| `testNegativeOffset` | true (`ReadAt`/`WriteAt` say "negative offset" without a system call; `Truncate(-1)` is EINVAL) | the plan is silent: the trusted models must return Go's error or be stuck, never pass a negative offset on |
| `testCASMapped` | **SIGSEGV** (amd64 `LOCK CMPXCHG` writes even when the compare fails; `code=0x2`, SEGV_ACCERR) | **not stuck today**: `CmpXchgBytesFailS` accepts cells with readers, so this probe is provable (unsound) until the plan's Perennial prerequisite lands |

## Probes (`twoways/`): neither `RET true` nor `RET false` may be provable

Each probe is a boot program. A setup boot ends in `waitForCrash` (`for {}`), so only a crash
ends it, and only the observing boot returns. Each phase is kept in synced bytes of a file that
an earlier crash has already kept, so the answer depends only on what the last crash did to the
byte under test.

| probe | decision | true is possible because | false is possible because |
|---|---|---|---|
| `bootUnsyncedData` | D1 | the model makes the unsynced byte arbitrary, which includes the written value; Linux may have written the page back | arbitrary includes the old value; Linux may not have written it back |
| `bootUnsyncedName` | D4 | a file that survives a crash keeps its synced byte; ext4 and xfs in practice make a new file's name durable on its fsync | the file was created since boot and no directory was synced, so the crash may drop it; POSIX promises nothing |
| `bootFailedThenSync` | D2 | the poisoned file's bytes are arbitrary after the crash | the same; on Linux, the first sync's failure may have dropped the dirty page and marked it clean, and the second sync then has nothing to write |
| `bootUnsyncedTruncate` | size range | the size after the crash is anywhere in `[sizeLo, sizeHi]` = [1, 4096] | the same. Linux usually keeps the new size, because the phase file's fsync commits the journal, but nothing promises it |

## Open points for the plan

The programs found these, in order of weight.

1. **D2 makes every crash property unprovable once a sync can fail** (P2 above).
   Environmental failure covers fsync, and `AngelicExit` does not stop the crash that
   follows. Under poisoning that crash makes long-durable bytes arbitrary. Linux loses only the
   pages whose writeback failed. The fix is either the adequacy premise "no fsync fails", or
   D2's precise alternative: the bytes dirty at a failed sync stay arbitrary until they are
   rewritten.
2. **bbolt's `WriteTo` (etcd's snapshot) is stuck.** With `WriteFlag` 0, it copies pages 2 up
   to `tx.Size()` with `ReadAt` on `db.file`, holding only its read transaction. Free pages in
   that range can be reallocated and rewritten by a concurrent writer. Their bytes in the copy
   do not matter, but in the model that PRead races an in-flight write, which is stuck. Proving
   `WriteTo` needs a racing PRead to return arbitrary bytes for the overlapping part, which is
   sound because Linux returns some mix. A racing load must stay stuck. With `WriteFlag` set
   (etcd may set O_DIRECT), the open is stuck too, and so is `sameFile`'s Stat if it races an
   extending write (D8, `NoGrowSync`).
3. **PRead racing a shrinking Ftruncate is more defined than Linux.** Ftruncate is one atomic
   step, so the model's PRead sees the old or the new size. Linux's read loop checks `i_size` page
   by page and can return a length between the two. bbolt never shrinks, so the simplest fix
   is to make a shrinking Ftruncate's range "in flight" for PRead (stuck), or to make a
   shrinking Ftruncate stuck altogether.
4. **bbolt's `init` is not crash-safe** (minibolt above). A proof of bbolt's crash safety needs
   the fork to sync pages 2–3 before the metas, or it must give up the property for a crash
   during init.
5. **A zero-length write past EOF** (`testWriteAtEmpty`). For `n = 0` and `off > size`, the
   plan's affected range `[size, off)` is not empty, and whether PWriteFinish with `k = 0`
   extends the file is unsaid. Go makes no system call there. The trusted `WriteAt` should
   skip PWrite when there are no bytes, or the step should not extend when `k = 0`. The plan
   should also say that a partial write with `0 < k < n` at `off > size` leaves size `off + k`.
6. **Negative offsets** (`testNegativeOffset`): unsaid. The trusted `ReadAt`/`WriteAt` should
   return Go's "negative offset" error, and `Truncate(-1)` should return EINVAL, or the call
   should be stuck.
7. **Smaller points.**
   - `O_RDONLY|O_TRUNC` is in the allowed flags. Linux truncates, so the plan should say so.
   - TRUNC should update `sizeLo` and the dirty set as Ftruncate does.
   - The plan should say that a file a crash keeps becomes `named`.
   - "Arbitrary errno" includes ENOENT for an existing file. That is sound, but a program
     cannot use ENOENT to test existence (the two-ways probes use the size instead). bbolt
     branches only on EWOULDBLOCK and ENOSYS, so it is unaffected.
   - The environment assumptions should add that the device writes sectors atomically and
     returns no media errors. The model's dirty set is per byte, so a torn sector that garbles
     a durable neighbour is outside it. A read error on a mapped page is SIGBUS on Linux, but
     the model lets the load succeed.
8. **Outside the file model:** the fork's `mmap` still sets
   `db.data = (*[common.MaxMapSize]byte)(unsafe.Pointer(&b[0]))`. That is the oversized
   array view that `unsafememory` replaces by `unsafe.Slice`, and it needs the same patch.
