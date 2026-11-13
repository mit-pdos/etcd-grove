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
