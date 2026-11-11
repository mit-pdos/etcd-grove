# Review, round 8: the per-byte semantics after round 7's fixes (branch `fs-bytes`)

**Date:** 2026-11-11. **Reviewed:** branch `fs-bytes` at `32e61a29e8` (round 7's fixes on
`12e1519ace`), the trusted semantics only: `GooseLang/Ext/Fs/{Impl,Tree,Paths,Lookup,Premises,
FilteredSem,SemOk,Tests}.lean`, `TrustedCode/{os,syscall}.lean`,
`TrustedCode/golang_org/x/sys/unix.lean` (against Go 1.27.3's `os`/`internal/poll` in
`/usr/local/go/src` and `golang.org/x/sys@v0.48.0` in the module cache), `examples/osfs/semantics/`,
and the clients `examples/osfs/{bboltfs,crashlog,walfs}/*.go` for the stuck rules.

**Method.** The `axiom` skill's, for a trusted semantics. Every rule that changes `cache`, `cand`,
`size`, `sizeLo`/`sizeHi` re-read against ext4 v7.0 and the round 4-7 measurements; every
trusted `os` model compared with the Go source line by line, looking for a path where the model
answers without asking the extension (no stuck step, no errno) while Go or Linux answers
otherwise. One kernel experiment, on C through `fs-config/mkfs-mount.sh` and `check.sh`:
`fs-v2-r8/run.sh WORKDIR` runs `fs-v2-r8/gocheck/` (output below). `lake build
GooseLang.Ext.Fs.Tests` passes, with no `sorry` (three `if_pos` deprecation warnings).

## Verdict

**The crash rule and the per-byte state: no outcome of Linux on C found that they exclude, and
no exploitable extra behaviour.** Round 7's fixes hold. `CacheOk` is proved for the start, all 27
step cases and the crash, and at most one change per file makes the announced values exactly
what lands. The stuck rules (one change per file, no empty `pwrite`, a mapped load or `mmap`
racing a change) are met by every client. The metadata half is unchanged since round 6. The
diff `e017084588..HEAD` touches no metadata rule, only docstrings and `FsInit`'s variable name.

**The trusted `os` model has three refutable gaps** (R1-R3). In each, `Seek`, `Write` or `Read`
returns success without making any extension call, where Go 1.27.3 on C returns an error every
time. So a three-line Go program that panics on that error gets a proof that it never panics.
No client reaches them: walfs seeks to 0, to the end and to an offset `Seek` returned, never
past 64 KiB, and no client writes an empty buffer or uses a closed file. They are still false
claims of the trust base. The rest are clarity items.

| # | severity | finding | where |
|---|---|---|---|
| R1 | unsound (no client reaches it) | `Seek(off, SEEK_SET/SEEK_CUR)` to any `n < 2^62` succeeds in the model; ext4 on C refuses every `n > 2^44 - 4096` (`s_maxbytes`) with `EINVAL`, measured. The `offMax` docstring says Linux fails only past the model's bound | `TrustedCode/os.lean:335-339, 353-375` |
| R2 | unsound (no client reaches it) | `File.Write` of an empty buffer on an `O_RDONLY` file returns `(0, nil)` in the model; Go issues `write(fd, p, 0)` and Linux answers `EBADF`, measured | `os.lean:388-404` (via `WriteAt`'s `len = 0` return, 316) |
| R3 | unsound (no client reaches it) | after `Close`: an empty `Write`, an empty `Read` and a `Seek` with `SEEK_SET`/`SEEK_CUR` succeed in the model; Go returns `ErrClosed` (`fdmu` lock / `incref`), measured. The module docstring says a closed file is stuck | `os.lean:24-27, 353-375, 388-404, 414-421` |
| F4 | doc-only / simplification | `open(O_TRUNC)` of a busy file is not stuck: its success branch is impossible, its failure branch with no effect is allowed. Sound (Linux serializes the truncate after the write), but the header, `OpenEffect`'s docstring and `data_inflight_changes.go` say "stuck" | `Impl.lean:57-60, 486-498, 584-593` |
| F5 | simplification | `Mmap`'s `¬ BusyAt` is a stuck rule nothing needs: `HeapRendered` already makes an in-flight byte's cell a hole | `Impl.lean:666` |
| F6 | doc-only | `File.Sync`'s docstring says "each failed attempt loses the writeback of the dirty bytes, D2, as on Linux", against no-failed-writeback and `Fsync`'s failure = no change. minibolt's `Commit` comment says the same (client text) | `os.lean:477-480`; `examples/osfs/bboltfs/minibolt.go:293-297` |
| F7 | doc-only | `data_short_io.go`: "a failed [pread] returns nothing" / "m <= 0, err != nil"; the step returns any prefix on failure, and `ReadAt.impl` copies it | `examples/osfs/semantics/data_short_io.go:13-16, 38-39`; `Impl.lean:594-601`; `os.lean:220-223` |
| F8 | doc-only (minor) | `sectorWhole_durable` assumes `h0` (every byte has a stamp-0 candidate). That holds in every reachable state (`ofDisk`, `announce` appends, `synced` replaces), but `CacheOk` does not carry it, so Premises' "never leaves a state without a crash" is argued, not proved | `Tests.lean:711-726`; `Premises.lean:52-54` |

## R1: `Seek` past ext4's maximum file size

**Model.** `File.Seek.impl` (`os.lean:353-375`) computes `n` from 0 (`SEEK_SET`) or from the
model's `off` (`SEEK_CUR`) with no extension call. It returns `EINVAL` only for a negative `n`,
and panics ("not modelled") only at `n ≥ offMax = 2^62`. For `0 ≤ n < 2^62` it returns `(n, nil)`,
deterministically. The `offMax` docstring (335-338) gives the reason "past it Linux's `lseek`
fails (`EINVAL` past the filesystem's maximum file size ...)". But ext4's maximum is far below
2^62.

**Linux on C.** `ext4_llseek` → `generic_file_llseek_size(..., maxbytes = s_maxbytes, ...)` →
`vfs_setpos`, which returns `-EINVAL` for `offset > maxsize`. For an extent file with 4 KiB blocks,
`ext4_max_size` gives `(2^32 - 1) · 4096 = 2^44 - 4096`. Measured (`fs-v2-r8/run.sh`, `TestSeekPastMaxBytes`):

```
Seek(0xffffffff000, SeekStart) = 0xffffffff000, <nil> (EINVAL: false)
Seek(0xffffffff001, SeekStart) = 0x0, seek .../seek: invalid argument (EINVAL: true)
Seek(0x100000000000, SeekStart) = 0x0, ... invalid argument (EINVAL: true)
Seek(0x4000000000000, SeekStart) = 0x0, ... invalid argument (EINVAL: true)
Seek(0x3fffffffffffffff, SeekStart) = 0x0, ... invalid argument (EINVAL: true)
```

**Counterexample program** (not built as an `axiomcx` package; Go side shown by the test):

```go
f, err := os.OpenFile(dir+"/f", os.O_RDWR|os.O_CREATE, 0o666)
if err != nil { return }
if _, err := f.Seek(1<<50, io.SeekStart); err != nil { panic("seek") }
```

Go on C panics every time. In the model, the `Seek` is pure code over the `file` cell, so a WP
proof of no panic takes a `wp_apply` of `OpenFile` and symbolic execution of `Seek.impl`.

**Writes past the bound are fine.** `WriteAt` at 2^50 gives `EFBIG` on C (measured: "file too
large"). The model allows success or any errno there, a superset that a proof cannot use.
`Truncate` and `Fallocate` past the bound are the same.

**Fix.** Use C's bound in `Seek.impl`: `EINVAL` for `n > 0xffffffff000`, Linux's exact answer,
measured, deterministic. Alternatively, a "not modelled" panic at that bound. Then correct the
`offMax` docstring: its bound stays for `Write`/`Read`, where the model is a superset anyway.
Better still, for uniformity: the header's discipline says "every step that makes a system call
may fail with any nonzero errno". `lseek` is the one system call the models answer
deterministically without the extension. Giving it an `ArbitraryInt` errno on top of the exact
`EINVAL` keeps the discipline uniform.

## R2: an empty `Write` on a read-only file

**Model.** `File.Write.impl` calls `WriteAt.impl`, which returns `(0, nil)` at once when
`len(b) = 0` (`os.lean:316`), with no extension call. `Write` then returns it.

**Go and Linux.** `File.Write` → `poll.FD.Write` (`internal/poll/fd_unix.go:365-395`) has no
empty-buffer shortcut: it calls `syscall.Write(fd, p[0:0])`. Linux's `vfs_write` checks
`FMODE_WRITE` before the count and returns `-EBADF`. (`WriteAt` is different: its loop does not
run for an empty buffer, so it returns `(0, nil)` without a call, as the model does.) Measured
(`TestEmptyWriteReadOnly`):

```
Write(nil) on O_RDONLY = 0, write .../ro: bad file descriptor (EBADF: true)
WriteAt(nil, 0) on O_RDONLY = 0, <nil>
```

**Program:** `f, err := os.Open(p); if err != nil { return }; if _, err := f.Write(nil); err != nil
{ panic("w") }`. Linux panics; the model proves no panic.

**Fix.** In `Write.impl`, model the empty case as the zero-byte `write(2)` it is. The simplest
form that keeps the model less defined than Linux: stuck unless the fd is a writable file's fd
(e.g. through a `PWriteStart`-like fd check, or a `FdKind`-style query extended with the
mode). Then return `(0, nil)` or any errno. Or mark it not modelled (a panic). No client writes
an empty buffer, but etcd's real encoder should be checked when the WAL is ported.

## R3: calls on a closed file that answer without the extension

**Model.** `Close.impl` sets `fd := -1`. The module docstring (`os.lean:24-27`) says a closed file
makes "the extension stuck on fd -1". That holds only for methods that reach the extension. Three
paths reach no extension op:
- `Seek` with `SEEK_SET` or `SEEK_CUR` (no `Fstat`);
- `Write` of an empty buffer (R2's path);
- `Read` of an empty buffer (`Read.impl` returns `(0, nil)` on `len = 0`, 420).

Each returns success.

**Go.** `pfd.Seek` → `incref`; `pfd.Write` → `writeLock`; `pfd.Read` → `readLock` before its
empty-buffer return. All three fail with `ErrFileClosing`, which `os` maps to `ErrClosed`. Measured
(`TestAfterClose`):

```
Write(nil) after Close = 0, write .../closed: file already closed (ErrClosed: true)
Read(nil) after Close = 0, read .../closed: file already closed (ErrClosed: true)
Seek(0, SeekStart) after Close = 0, seek .../closed: file already closed (ErrClosed: true)
WriteAt(nil, 0) after Close = 0, <nil>
ReadAt(nil, 0) after Close = 0, <nil>
```

`WriteAt` and `ReadAt` on an empty buffer return `(0, nil)` in Go too, so the model is right for
them.

**Fix (uniform).** Start every method model whose Go method takes the fd lock or `incref` with
`Truncate.impl`'s guard (`os.lean:467`): `if fd < 0 then Panic "... of a closed file not
modelled"`. That covers `Seek`, `Write` and `Read`. Or start them with an `FdKind` query, which is
stuck on -1. Either way, the docstring's claim then holds by construction.

**Also tried:** `Seek` of a directory fd after `Readdirnames` (`TestDirSeek`). Go returns
`(5, nil)`, as the model does: no finding.

## F4: `open(O_TRUNC)` of a busy file fails instead of being stuck

`OpenEffect`'s file case requires `trunc = true → ¬ BusyAt st i` (`Impl.lean:495`), so the
success branch is impossible while a change is in flight. The `Open` step's failure branch,
`st' = st0` with any errno (592-593), has no such premise, so the step is not stuck: it returns
an error. That is sound. ext4's buffered `pwrite` holds `i_rwsem` for the whole call, and
`do_truncate` takes it too. So in every Linux run where an `O_TRUNC` open overlaps a write, the
truncate happens after the write, which is a model run with the `Open` step after
`PWriteFinish`. The model's extra failure is extra behaviour. But the header ("a change's first
step is stuck while another is in flight"), `OpenEffect`'s docstring ("as every change, stuck")
and `data_inflight_changes.go` ("an open with O_TRUNC is stuck") say otherwise.

**Fix.** Lift the guard into the step: add `trunc → ∀ i, st.lookup p = some (.file i) → ¬ BusyAt
st i` to `Open`'s premises, so that it is stuck as documented. Or change the three texts to "fails".
The first is the uniform choice (every change's first step stuck).

## F5: `Mmap`'s `¬ BusyAt`

`Mmap` is stuck while a change is in flight on the file (`Impl.lean:666`). Nothing needs this.
`HeapRendered` gives a new mapping's cells `Free (cellVal ...)`, and `cellVal` is a hole on
`InflightAt` bytes, so a load racing the change is stuck anyway. No client needs the `mmap`
itself to race a change: minibolt remaps only from the writer, with nothing in flight. Dropping
it removes one special case from the header's "Races" and from `data_inflight_changes.go`.
Keep it only if a program-logic proof relies on it (none was checked here).

## F6-F8: text

- **F6.** `File.Sync`'s docstring (`os.lean:477-480`): "each failed attempt loses the writeback of
  the dirty bytes, D2, as on Linux". Since round 5, the semantics assumes no failed writeback,
  and a failed `Fsync` changes nothing. Also, `Fsync` never returns `EINTR`, so the retry is
  reachable only for `DirSync`. Say so. minibolt's `Commit` comment ("its bytes are lost, plan
  D2") is the same old reading, in client text.
- **F7.** `data_short_io.go` describes a failed `pread` as returning nothing. The step
  (`Impl.lean:600-601`) returns any prefix with a nonzero errno, and `ReadAt.impl` copies it into
  `b` without counting it (`os.lean:220-223`). The file's "Allowed" line should say so.
- **F8.** `sectorWhole_durable` takes `h0` as a hypothesis. Adding "every byte has a candidate
  stamped 0" to `CacheOk` (one line per case, as for the others) would prove Premises' claim that
  the premise never leaves a state without a crash, per file.

## What survives (attacks tried)

- **Page cache among candidates.** `CacheOk` is proved for the start, every step and the crash.
  `land` writes only announced values. With one change per file, the size is constant while a
  write with a gap or a resize is in flight, so round 7's cross-rule argument is no longer needed.
- **Sync against a change in flight.** Mechanism B (`fsync` racing a write) and a write that
  starts and finishes inside an `fsync`: the model can place the atomic `Fsync` step before the
  change's start unless the change happens-before the call. Busy bytes keep their history.
  `sizeLo = sizeHi = size` is widened again by `land`, and by the crash's in-flight disjunct while
  the change is in flight. No interleaving was found that needs a candidate the model drops.
- **Stale bytes past EOF in the last page.** `synced` collapses them to the page cache's stale
  value. ext4's writeback zeroes them (`ext4_bio_write_folio`), so the disk may hold 0 where the
  model has only the stale value. This is invisible: those bytes can come back only after an
  extension, and every extension announces 0 there (`resized`, `ofWrite`'s gap, `ofResize`;
  measured zero-filled, `fs-v2-f3/f3.sh`).
- **Failed and short writes.** Linux never lands bytes with an error return
  (`generic_perform_write` returns the count written if any). The model's prefix-with-errno is a
  superset. Go's `EINTR` retry after a landed prefix rewrites the same range.
- **`fallocate`.** Mode 0 within the size announces nothing (correct: holes and unwritten extents
  read zeros). Mode 0 past EOF with a gap: zeros announced from the old size. A partial failure:
  any `w` in `[size, target]`, which covers ext4's per-chunk size updates. `KEEP_SIZE`: no change.
- **Stuck rules against the clients.**
  - minibolt: the writer makes every change (`Truncate`, `WriteAt`, `Fdatasync`) and every
    `mmap`. `Get`'s mapped loads are on pages of its committed transaction, disjoint from the new
    page and outside metalock's meta writes. `Snapshot`'s `ReadAt` races `Truncate`'s growth and
    the `WriteAt`s; `StatSees`/`ReadSees` allow it, and the size seen never drops below the
    transaction's pages.
  - crashlog: one thread.
  - walfs: one thread. `Fallocate` mode 0 and `KEEP_SIZE`, `Truncate` (shrink) then `Fallocate`
    (ZeroToEnd), all sequential.
  - No client uses `O_TRUNC` or `os.Create`. `WriteAt`/`Write` never pass empty data to
    `PWriteStart`; R2 is the other side of that rule.
- **x/sys v0.48.0.** `Fallocate` (one `Syscall6`, no `EINTR` retry), `Mmap`/`Munmap` (the
  `mmapper` code as quoted) and `FcntlFlock` (one `fcntl`) match their models.
- **Metadata.** Unchanged since round 6 (diff checked). Spot re-checks: `Open` on a directory with
  `O_CREAT` (failure only, Linux `EISDIR`); `Rename` onto a non-empty directory (failure);
  `LstatDir`'s cases against Go's `Rename`; `DirSync` racing a rename (jbd2's force-commit covers
  any handle already stopped). No finding.

## Not done

No Lean counterexample for R1-R3: each needs an `axiomcx` Goose project. The Go side is
measured, and each model path is plain code with no extension step, so the proof is direct. The
program logic (`Specs.lean`, ...) was not reviewed. On this branch no Lean file under
`GooseLang/` or `Proof/` refers to `Seek.impl`, `File.Write.impl` or `File.Read.impl`, so no
proof uses R1-R3 yet. No new crash experiment: no finding
depends on a crash behaviour not measured in rounds 4-6.
