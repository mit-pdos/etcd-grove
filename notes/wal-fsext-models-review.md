# Review: the WAL's new trusted models over fsExt (branch `wal-models`, 536fa3517a)

Scope: `LinuxFs/TrustedCode/{os,syscall}.lean` diffs against `origin/wal-int` (`syscall.Fallocate`,
`syscall.FcntlFlock` with `F_OFD_GETLK`, `model.stat`/`Stat`/`Lstat`, `fileStat.Mode`/`arbitraryMode`,
`MkdirAll`, `RemoveAll`/`model.removeAllFrom`, nil `File.Close`, empty `File.Write`, translated
`WriteFile`), their Go examples `examples/osfs/semantics/model_*.go` and `models_test.go`, read against
`GooseLang/Ext/Fs/Impl.lean` (same branch) and the Go 1.27.3 sources
(`~/go/pkg/mod/golang.org/toolchain@v0.0.1-go1.27.3.linux-amd64/src`: `os/path.go`,
`os/removeall_at.go`, `os/root_unix.go`, `os/file_unix.go`, `os/dir_unix.go`,
`internal/poll/fd_unix.go`, `syscall/flock_linux.go`, `syscall/zsyscall_linux_amd64.go`).

Experiments: `/home/ubuntu/.claude-E/jobs/af0ee947/tmp/models-review/` (`removeall/main.go`,
`mt/extra_test.go` plus a copy of `models_test.go`), run on this machine's `/` (ext4, Linux
7.0.0-38). `notes/axiom-review/fs-config/check.sh /` reports "/ is C". I did not use a loop mount
from `mkfs-mount.sh`. All of the branch's `models_test.go` tests pass here.

Verdict: **READY WITH CHANGES.** I found no Linux outcome that the models exclude and that a
proved program could reach. One vacuity is serious: as drafted, `MkdirAll` cannot be proved for any
caller. The other findings are minor.

---

## 1. Vacuity (severe): `MkdirAll` goes above the roots after spurious `Stat` failures, and gets stuck

**Model.** `MkdirAll.impl` is Go's `path.go` body. Its fast path is `Stat(path)`. When that fails, it
recurses on the parent. Every `Stat` (`model.stat`, through the extension's `Open`) may fail with any
errno on any path, existing or not. That is the extension's environmental-failure rule: the `Open`
failure branch has no premise. So this execution of the model is always possible for
`MkdirAll(r + "/wal")`, where `r` is a root (say `/data/r`):

1. `Stat(/data/r/wal)` fails with EIO, which is allowed.
2. The model recurses with parent `/data/r`. `Stat(/data/r)` fails with EIO, which is also allowed.
3. The model recurses with parent `/data`. `Stat(/data)` calls `Open` on a path that is not a
   `TreePath`, so the step is **stuck**.

For a one-component root `/r`, the parent is `""`, so the model skips the recursion and calls
`Mkdir("/r")`. The extension's `Mkdir` requires `TreeName` (strictly below a root), so that step is
**stuck** too.

The same happens for any depth below the root: every `Stat` on the chain can fail, so the stuck
execution is reachable from every call. No WP of `MkdirAll` exists. That makes these unprovable:
fileutil's `TouchDirAll` (its `Exist(dir)` can fail, then it calls `MkdirAll(dir)`), `CreateDirAll`,
and `wal.Create`. The plan's TouchDirAll spec (`dirDurable parent`, `d ∉ area`) gives no way out,
because the failure is unconditional.

**Linux.** Go keeps going above the root. `stat("/data")` succeeds, or fails with no effect.
`mkdir("/data/r")` fails with EEXIST, and `lstat` then sees a directory. So `MkdirAll` returns nil or
an error, and has no effect on the trees. That holds because the roots and their ancestors exist as
directories, and the environment says no other process moves a directory above a root.

**Fix.** At a path that is not a `TreeName` (a root or one of its ancestors), `MkdirAll` should make
no extension step:
- Run Go's control flow with `Stat`, `Mkdir` and `Lstat` answered arbitrarily.
- Or, more simply, return nil or `&PathError{"mkdir", p, Errno(e)}` for any `e` and any prefix `p` of
  the path. Those are the only errors Go can return from that part of the call.

The recursion from a `TreeName` path only reaches its parent, which is a `TreeName` or a root. So the
model needs one query of its state, like `FdKind`: is `p` a `TreeName`? Alternatively, add an
extension rule that path calls on a root or an ancestor of one answer with no effect.

Justify it by the environment: the roots and their ancestors are existing directories throughout,
which the environment should state explicitly. Add a Go example per the semantics-examples rule.

## 2. Minor (soundness, theoretical): `F_OFD_GETLK` leaves the padding alone, but Linux writes the whole struct back

**Model.** On success, the model stores arbitrary values into `Type`, `Whence`, `Start`, `Len` and
`Pid`, and never touches `Pad_cgo_0` or `Pad_cgo_1`.

**Linux.** In `do_fcntl`, the `F_OFD_GETLK` case is `copy_from_user(&flock, argp, sizeof flock)`,
then `fcntl_getlk`, then `copy_to_user(argp, &flock, sizeof flock)`. That writes back every byte,
padding included, with the values read at entry.

**Program.** Goroutine A calls `syscall.FcntlFlock(fd, unix.F_OFD_GETLK, &lk)`. Goroutine B writes
`lk.Pad_cgo_0 = [4]byte{1, 2, 3, 4}` during the call; padding is a separate field, so this is not a
Go data race. Linux can revert B's write. The model cannot: B's write persists, and the model does
not even count it as a race, because it never accesses the padding.

No client does this; fileutil's `getlk` is a local. The existing `TestOFDGetlkPadding` only checks
the case with no concurrent writer.

**Fix.** Load the whole struct at entry and store all seven fields at the end (the padding as
loaded), so a concurrent access is a race the proofs must exclude. Otherwise, drop the claim
"the padding is left as it is" and say it is reverted.

## 3. Minor (the justification is incomplete; the model is sound): RemoveAll's "one read per pass" is not why it contains Go's runs

**The doc's argument.** The docstring of `model.removeAllFrom` says Go's 1024-name chunks "read the
same names across the pass".

**Why that is false under concurrency.** Go's pass handles only one chunk. It breaks out of the inner
loop unless all 1024 removals failed, closes the directory, and reopens it. Entries created meanwhile
are read in the next pass, mixed with the remaining old entries.

**Measured** (`removeall/main.go`). Directory `D` holds 1100 files. Goroutine T2 waits until some
original file is gone, creates `D/X`, records the originals still present (about 900), and polls.
In **20 of 20 runs**, `X` was removed while an original that existed before `X` was created
(`f0002`, ...) was still present. `RemoveAll` returned nil.

**Why the model still contains this run.** In the model, pass 1 reads every name and removes every
name. Pass 1's read ended before its first unlink, so it cannot return `X`. The model reproduces Go's
run only through no-effect failures of pass 1's unlinks with ENOENT, which `removeAllFrom` treats as
success (no error recorded). The names come back in pass 2, mixed with `X`.

The model is sound, but that is the load-bearing reason, and the doc should say so. A later
tightening of the extension's `Unlink` failure branch (for example, "ENOENT only when no entry")
would silently make RemoveAll's model unsound.

**More faithful alternative.** Let a pass's read stop at an arbitrary point (a chunk), remove those
names, then either read on from the same fd (Go's all-failed case) or close and reopen.

## 4. Minor (stale trusted documentation)

The `Impl.lean` header, lines 80-81, still says "the `os` model's empty `Write`, which Go does issue,
is not modelled". It now is (`File.Write.impl`, `model_os_writefile.go`). Per CLAUDE.md, a semantics
change updates its documentation in the same commit.

## 5. Vacuity (minor): non-canonical paths are stuck

`Stat`, `Lstat`, `MkdirAll` and `RemoveAll` of a path that is not canonical are stuck. That covers a
trailing slash, `a//b`, relative paths and `..`. This follows the extension's discipline, but note
what Go does there (measured, `TestReviewRemoveAllUnderFile`): `os.RemoveAll("<d>/f/")`, where `f`
is a file, **removes `f`**, by way of `splitPath` and `unlinkat(parent, "f")`. Clients must pass
cleaned paths. The WAL does (`filepath.Clean(dirpath) + ".tmp"`, `filepath.Join`).

## 6. Minor: `Lstat = Stat` assumes the root's own path is not a symlink

`RootForm` and the environment exclude symlinks *in the roots' trees* ("every entry ... regular file
or directory"). Nothing excludes a root path whose last component is a symlink to a directory. For
such a root, `lstat(root)` reports `ModeSymlink`, and the model says `ModeDir`.

Today `Lstat(root)` is reachable only through `MkdirAll`'s branch after a failed `Mkdir`, which is
stuck at a root anyway (finding 1). It matters if the fix for finding 1 keeps `Lstat` at a root.
Either state in the environment that no root path is a symlink, or answer arbitrarily at roots.

## 7. Minor (process): `models_test.go` measurements are not tied to configuration C

The tests run in the package directory (the machine's `/`). They do not run on a `mkfs-mount.sh`
filesystem or call `c_check`. `doc.go` says the measurements cited "were made on C with the
scripts". `check.sh /` does accept this machine's `/`, although its `discard` option and the
cloud-image `mkfs` features (`metadata_csum_seed`, `orphan_file`) are not `mkfs.ext4` defaults.

None of the claims plausibly depend on that. Still, either run the tests under `c_mkfs`/`c_mount`,
or have them call `check.sh` on the filesystem they use and record its output, as the rule requires.

## 8. Info (sound): the lock commands return where Linux blocks forever

`F_SETLKW` and `F_OFD_SETLKW` (`ofdLockFile`) return any errno at once. On Linux they can block
forever: for example, a second `LockFile` of the same file through another open file description in
the same process (OFD locks conflict within a process), or another etcd holding the lock. For safety
this only adds behaviours, and Perennial proves no liveness. The model gives no mutual exclusion, so
no proof can rely on the lock (Q1, deferred).

## 9. Info (sound): extra outcomes of an empty `Write`

The empty `Write` may return EINTR, which Go never returns (`ignoringEINTRIO`). It may also return
`(0, nil)` on a read-only or directory fd, where Linux answers EBADF (measured,
`TestReviewEmptyWriteDir`). These are extra outcomes only. Linux's zero-byte `write` to an ext4 file
has no effect: `generic_write_checks` returns 0 before `file_modified`, so the "no extension step"
claim holds.

---

## Checked and found sound

- **`Fallocate`.**
  - It is the same stub as `unix.Fallocate`: `Syscall6`, `errnoErr`, EINTR not retried.
  - Modes 0 and 1 map correctly to `FallocStart`/`FallocFinish` and `FallocKeep`. A grow that
    fails part way is a prefix, and fileutil then falls back to truncate.
  - Misuse is stuck. Measured: a read-only fd gives EBADF in both modes; `len` 0 gives EINVAL. An
    `off+len` overflow gives EFBIG, which the model covers among its extra outcomes.
- **`FcntlFlock`.**
  - The command numbers are right (6, 7, 36, 37, 38).
  - `F_OFD_GETLK` on any fd: measured, a pipe and a directory give `(nil, F_UNLCK)`, and a nonzero
    `Pid` gives EINVAL with the struct unchanged. On failure, nothing is written back (the kernel
    does not reach `copy_to_user`), as the model says.
- **`model.stat`.**
  - An `open` with `O_RDONLY|O_CLOEXEC` and no `O_CREAT` or `O_TRUNC` has no effect in the model, is
    never stuck on a `TreePath`, and can succeed wherever `stat` does. The model does not model
    permissions. Measured: a mode-000 directory is `stat`-able, while `open` of it gives EACCES; the
    model may let the open succeed.
  - FIFOs, devices, sockets and mount points are excluded by the environment, only inside the trees.
  - Fd numbers: the model can choose any free fd, so a concurrent `Open` can still get the fd Linux
    would give it.
  - Mode bits: `0xD001FF` matches `fillFileStatFromSys` (`0777`, setuid `1<<23`, setgid `1<<22`,
    sticky `1<<20`), with `ModeDir = 1<<31`.
- **`MkdirAll`'s control flow** otherwise matches `path.go` line by line, including:
  - `&&` short-circuits (Perennial `Notation.lean`);
  - ENOTDIR for an existing non-directory, and for a file in the middle of the path;
  - the EEXIST race resolved through `Lstat`.
- **`RemoveAll` against `removeall_at.go` and `root_unix.go`.**
  - The cases for `""` and `"."` are right.
  - `Remove`'s choice between the two errnos is right.
  - `OpenFile(parentDir)` and its errors are right.
  - `openDirAt` and its errors: a file's fd is answered ENOTDIR, which is right, and the
    ENOTSUP-to-ENOTDIR translation is reachable through the choice of errno.
  - The `readdirent` errors carry `base`, which is right: `newDirFile(fd, name)` names the file
    `base`.
  - The `IsNotExist` checks, the error prefixing, and the `recurseErr` handling across passes are
    right.
- **The RemoveAll guard.**
  - Path names and fd-relative names agree unless a directory is renamed, which the guard makes
    stuck.
  - The guard is also enough for the rmdir-and-recreate case. A directory can only be removed when
    empty, so a removed ancestor is dead, and every `*at` call through it fails with ENOENT
    (getdents on a dead directory is ENOENT too). The model's no-effect failures can reproduce that.
  - The guard is ended on every path.
  - Its cost: any directory rename anywhere in the trees by another thread during `RemoveAll` is
    excluded. The WAL's uses are sequential.
- **nil `File.Close`** returns `os.ErrInvalid` (the global is translated). **`WriteFile`** is
  translated as Go 1.27.3's body.

---

## Dispositions (2026-11-13, branch `wal-models`)

The trusted changes below are **pending the user's review** (marked so in their docstrings).

1. **MkdirAll above the roots (serious): fixed** (`03de18e9ca`). The extension gains a query that is
   not a system call, `PathKind` (`GooseLang/Ext/Fs/Impl.lean`): `#p ↦ #1` for a `TreeName`, `#0`
   for a root or an ancestor of one (`OsState.AtOrAboveRoot p := p ≠ [] ∧ ∃ rj ∈ roots, IsUnder p
   rj.1`), stuck otherwise; `st' = st`. `MkdirAll.impl` asks it first; at `0` it runs
   `model.mkdirAllAbove`, Go's body with no extension step (`Stat` a directory or any error; the
   recursion on the parent; `Mkdir` failing; `Lstat` a directory, or `&PathError{"mkdir", path,
   Errno(e)}`, `e` any nonzero errno). The parent computation is shared (`model.mkdirAllParent`).
   The environment (the header) now says the roots and their ancestors are existing directories
   throughout, a root no symlink. Go example `model_os_mkdirall_above.go` (and `env_roots_only.go`),
   measured by `TestMkdirAllAboveRoot`. WP spec `wp_osPathKind` (`TreeSpecsDirFd.lean`), proved.
   `Stat`/`Lstat` at a root already answer (`Open` takes a `TreePath`); above a root they are
   stuck as every step on a path outside the trees, which no model now reaches on its own: left as
   is. `RemoveAll` at or above a root stays stuck (Linux would delete the root's tree, and maybe
   the root, which the environment excludes); documented.
2. **`F_OFD_GETLK` padding: fixed** (`5284132963`). The model loads all seven fields of `*lk` at
   entry and on success stores all seven, the padding as loaded (`model.flockPad`); docstring and
   `model_syscall_fcntlflock.go` cite `do_fcntl`'s whole-struct copies.
3. **RemoveAll's justification: fixed** (`13787b01ae`). The docstring of `model.removeAllFrom` now
   describes Go's chunk-then-reopen passes and gives the load-bearing reason: the extension's
   `Unlink`/`Rmdir` may fail with `ENOENT` and no effect, which is success here; it warns that
   tightening those failure branches would make the model unsound. The more faithful chunked model
   was not adopted.
4. **Stale header line: fixed** (`8408ca3774`).
5. **Non-canonical paths: documented** (`03de18e9ca`): in `model.stat`, `MkdirAll.impl`,
   `RemoveAll.impl` (with the `RemoveAll("<d>/f/")` example) and `env_roots_only.go`. The WAL's calls
   (`wal.go`: `os.RemoveAll(tmpdirpath)`, `os.RemoveAll(w.dir)`, `fileutil.CreateDirAll(tmpdirpath)`,
   `Exist`/`TouchDirAll(dir)`) are on its directory and `filepath.Clean(dirpath) + ".tmp"`,
   canonical when its directory is: the vacuity is not reached.
6. **`Lstat = Stat` at a root: fixed by the environment** (`03de18e9ca`): "a root is no symlink"
   (ancestors may be, which `mkdirAllAbove`'s error outcome covers).
7. **`models_test.go` on C: fixed** (`03de18e9ca`). `run-models-on-c.sh` makes a filesystem with
   `mkfs-mount.sh`, records `check.sh`'s output and runs the tests there (`$SEMANTICS_C_DIR`). Run
   2026-11-13: "check: /tmp/…/mnt is C (kernel 7.0.0-38-generic, ext4, block size 4096, …)"; all 8
   tests pass (needs `sudo`, which this machine has).
8. **Lock commands return where Linux blocks: no change** (sound; Q1 stays deferred).
9. **Extra outcomes of an empty `Write`: no change** (sound).

---

## Above-root Stat/Open (2026-11-13, branch `wal-above`)

**Finding** (W4 sixth session, `notes/wal-fsext-plan.md`): `os.Stat` and `os.Open`/`OpenFile` of a
strict ancestor of a root were stuck (the extension's `Open` needs `TreePath`), and `fileutil.TouchDirAll`'s
`Exist` loop (which climbs while `Stat` fails; the model lets `Stat` of the root fail) and its `syncDir`
loop can reach a root's parent, so their proofs would be vacuous. The changes below are trusted and
**pending the user's review**. Commits: `93d9757a8a` (extension), `5a5cdbb621` (os models, Go
examples), `a6214a8322` (specs and proofs).

### Trusted text (`GooseLang/Ext/Fs/Impl.lean`)

* Header, "Environment": "Only paths in the roots' trees are given a meaning: a step on any other
  path is stuck, but for the queries `PathKind` (at or above a root) and `Open`'s outside case (a
  read-only `open` of a strict ancestor of a root, whose fd only `fsync`s, with no claim on what that
  makes durable, and closes)."
* `ProcState` gains `ofds : GMap w64 Unit := ∅` ("the fds of directories outside the roots' trees (a
  strict ancestor of a root, `Open`'s outside case): the model knows nothing of them but that they are
  open"); `ProcState.empty` sets it `∅` (so a crash forgets them, as the rest of the process).
* `OsState.AboveRoot p := p = [slashB] ∨ (p ≠ [] ∧ ∃ rj ∈ st.fs.roots, (p ++ [slashB]).IsPrefix rj.1)`
  (`/`, or `/c₁/…/cₖ` with `/c₁/…/cₖ/` a prefix of a root). (`AtOrAboveRoot` is now unused; to remove
  with the next change of the file.)
* `FdFree st fd` adds `st.proc.ofds !! fd = none`. `OsState.addOfd`/`delOfd` insert/delete in `ofds`.
* `OpenOutside v st e' st'` (an `abbrev`), the **second disjunct of `"Open"`**:
  `∃ p fl t start, v = PairV (osTokV t) (PairV #p #fl) ∧ ¬ st.TreePath p ∧ st.AboveRoot p ∧
  (fl.toNat = O_RDONLY ∨ fl.toNat = O_CLOEXEC) ∧ st.proc.calls !! t = some start ∧
  ((∃ fd, FdFree st fd ∧ st' = (st.metaEnd t).addOfd fd ∧ e' = osRes #fd 0) ∨
   (∃ e ≠ 0, st' = st.metaEnd t ∧ e' = osRes #(-1) e))`. Other flags at such a path: stuck.
* `"FdKind"`: a third answer, `#2`, when `fds !! fd = none ∧ dfds !! fd = none ∧ ofds !! fd = some ()`.
* `"OutSync"`: `#fd ↦ #e`, any `e` (0 included), `ofds !! fd = some ()`, `st' = st` (no claim on
  durability: on C a directory fsync commits its filesystem's journal, which may be another
  filesystem's; claiming nothing is weaker than either).
* `"OutClose"`: `#fd ↦ #e`, any `e`, `ofds !! fd = some ()`, `st' = st.delOfd fd`.
* `"PathKind"`: `#1` for a `TreeName`; `#0` for a root (`¬ TreeName p ∧ ∃ rj ∈ roots, rj.1 = p`);
  `#2` for a strict ancestor (`¬ TreePath p ∧ AboveRoot p`, `/` included: before, `/` was stuck);
  stuck elsewhere.

### Trusted text (`LinuxFs/TrustedCode/os.lean`)

* `model.stat op name`: first `if PathKind name = 2 then model.statAbove op name else` (the old body).
* `model.statAbove op name` (no extension step): `if ArbitraryInt = 0` then a fresh `fileStat` with
  `size := ArbitraryInt`, `mode := arbitraryMode (if ArbitraryInt = 0 then ModeDir else ModeSymlink)`,
  nil error; else a nil `FileInfo` and `&PathError{op, name, Errno(m)}` (`m := ArbitraryInt`, `2` if
  it is 0). Linux: `stat` follows a symlink ancestor (a directory), `lstat` may see the symlink; either
  may fail; the model's extra answer (Stat seeing a symlink) only weakens.
* `File.Sync.impl`, `File.Close.impl`: `kind = 0` → `Fsync`/`Close`, `kind = 1` → `DirSync`/`DirClose`,
  otherwise `OutSync`/`OutClose`.
* `MkdirAll.impl`: the above branch is taken at `PathKind ≠ 1` (was `= 0`), so a root's strict
  ancestors (now `2`) still take `model.mkdirAllAbove`.
* `OpenFile.impl` is unchanged (it calls `Open`, whose outside case answers above the roots).

### Go examples and measurements

`examples/osfs/semantics/model_os_stat_above.go`, `model_os_open_above.go` (indexed in `doc.go`);
`models_test.go`'s `TestStatOpenAboveRoot`, run on C by `run-models-on-c.sh` (2026-11-13: "check:
…/mnt is C (kernel 7.0.0-38-generic, ext4, block size 4096, …)"; `TestStatMode`,
`TestMkdirAllAboveRoot`, `TestStatOpenAboveRoot` pass): `Stat`/`Lstat` of `/` and of a root's parent
succeed with a directory; `open(O_RDONLY|O_CLOEXEC)` of either succeeds, `fsync` and `close` return 0;
`O_WRONLY`/`O_RDWR` fail with `EISDIR`; the directory's inode, link count and mtime unchanged; `Lstat`
of a symlink to a directory sees a symlink, `Stat` a directory.

### Untrusted (ghost and proofs)

* The outside fds' ghost: `OsGS.γo` (`w64 ↦ Unit`), `ofdCtx` (`⌜OfdDisj st⌝ ∗ gAuth γo ofds`) a third
  conjunct of `osCtx`; `osOutFd fd` its whole fragment (`TreeSharedOut.lean`). The generic lifts
  (`wp_fs_stepT/M/TC`, the variable-op wrappers) take `o ≠ "OutClose"` (an auto-param, `by decide`):
  every other step keeps `OfdDisj` and adds at most a fresh outside fd (`isFsStep_ofd`, CommitMono.lean),
  whose ghost entry the generic lift makes and drops; `wp_fs_stepO` exposes `ofdCtx`.
* Proved (no `sorry`): `wp_osOpenAboveS`, `wp_osFdKindOut`, `wp_osOutSync`, `wp_osOutClose`
  (`TreeSharedOut.lean`), `wp_osPathKindAboveS` (`PathKindS.lean`), `os.model.wp_stat_aboveS`,
  `os.OpenFile/Open.wp_aboveS`, `os.File.Sync/Close.wp_outS` (`NsAbove.lean`);
  **`os.Stat.wp_proofAboveRoot`** (`Proof/os/StatAbove.lean`), `fileutil.OpenDir.wp_proofAboveRoot`,
  `fileutil.Fsync.wp_proofOutS`, **`fileutil.syncDir.wp_proofAboveRoot`**.

## fileStat.Name (2026-11-13, branch `wal-above`)

**Finding** (`wal-read5`, W3/W5 log): the model's `fileStat` had no name and `Name()` no body (stuck),
but the WAL's decoder calls `FileInfo().Name()` for its "frame too large" error. Trusted, **pending
the user's review**:

* `LinuxFs/TrustedCode/os.lean`: `fileStat` gains `name' : GoString` (first, as Go's);
  `fileStat.underlying` is `struct{ name string; size int64; mode FileMode }`;
  `fileStat.FieldAssumptions` gains `get_name`/`set_name`. New `model.base path`: `"."` for `""`,
  else `path[len(mkdirAllParent path)+1:]`, or `path` itself if that is empty (`/`): Go's
  `filepathlite.Base` on the canonical absolute paths the model takes. `File.Stat.impl` stores
  `model.base f.name`, `model.stat` and `model.statAbove` `model.base name` (as
  `fillFileStatFromSys`, `stat_linux.go`: `fs.name = filepathlite.Base(name)`). `model.mkdirAllParent`
  moved up the file (unchanged).
* `LinuxFs/Code/os.toml`: `fileStat.Name` translated (`return fs.name`); `Code/os.lean` regenerated
  (`etc/goose.py --project bboltfs`: `fileStat.Name.impl`, `ptr_Name_unfold`).
* Go example `examples/osfs/semantics/model_os_filestat_name.go`; `TestFileStatName` on C (pass):
  `Stat(d/wal).Name() = "wal"` (and `Lstat`), `Stat("/").Name() = "/"`, `f.Stat().Name()` the file's
  base name.

Untrusted: `ownFileStat` also holds `∃ name, name ↦□ name`; `os.fileStat.Name.wp_proof`
(`Proof/os/fileStat__Name.lean`) proves the `wal-read5` hypothesis spec `os.fileStat.Name.spec`;
`os.model.wp_base` and the `parentModel` lemmas moved to `Proof/os/PathParent.lean`; users repaired
(`StatS`, `File__Stat`, `fileStat__Size`, `MkdirAll*`, `NsAbove`, `ReadBridge`'s `ownFileStat_persist`).
`ReadBridge` still takes `wp_Name` as a hypothesis: its callers can now pass `os.fileStat.Name.wp_proof`.
