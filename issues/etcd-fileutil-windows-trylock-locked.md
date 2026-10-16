---
upstream: known
checked: 2026-10-16
links:
  - etcd-io/etcd#14252 issue closed: this bug (restart fails with "wal: file not found" on Windows after the purger deleted WAL files the WAL held; diagnosed by ahrtr, closed by the stale bot)
  - etcd-io/etcd#14293 pr closed: a fix of `lockFile`'s error mapping, closed unmerged
  - etcd-io/etcd#14300 pr merged: improves the WAL file error message only; does not fix the lock
---

# fileutil (Windows): `TryLockFile` on a locked file succeeds, so the WAL purger deletes WAL files the WAL still holds

- **Status**: a bug (Windows only; a wrong result of `TryLockFile`, which breaks the lock protocol
  between the WAL and the file purger; after enough WAL rotations before a snapshot, the member
  cannot restart). Windows is a Tier 3 (untested) platform upstream.
- **Where** (etcd pin `107edf7e4`): `client/pkg/fileutil/lock_windows.go:84-97` (`lockFile`):

  ```go
  err := windows.LockFileEx(fd, flags|windows.LOCKFILE_EXCLUSIVE_LOCK, 0, 1, 0, &windows.Overlapped{})
  if err == nil {
      return nil
  } else if err.Error() == errLocked.Error() {
      return ErrLocked
  } else if err != windows.ERROR_LOCK_VIOLATION {
      return err
  }
  return nil
  ```

  `TryLockFile` (`lock_windows.go:30-40`) passes `LOCKFILE_FAIL_IMMEDIATELY`, so a file another
  handle has locked fails with `ERROR_LOCK_VIOLATION`. `errLocked` (`:28`) is the lower-case text
  without a period, while Go's `Errno.Error()` returns the system message as `FormatMessage` gives
  it ("The process cannot access the file because another process has locked a portion of the
  file."), so the second branch never matches, and the last line maps `ERROR_LOCK_VIOLATION` to
  `nil`: success. The caller that depends on it is `purgeFile` (`client/pkg/fileutil/purge.go:69-76`),
  which removes a WAL file only after `TryLockFile` succeeds; the WAL keeps every file it still
  needs locked (`server/storage/wal/wal.go:253`, `:855`) and releases them only up to a saved
  snapshot (`WAL.ReleaseLockTo`, `wal.go:909`, through `storage.Release`,
  `server/storage/storage.go:78`). The server starts the purger at `server/etcdserver/server.go:607`
  (`PurgeFileWithDoneNotify`, with the lock).
- **What happens**: on Windows, once more than `--max-wals` WAL files exist, the purger deletes the
  oldest ones even while the WAL holds them (`CreateFile` opens with `FILE_SHARE_DELETE`, so the
  delete succeeds). If the WAL rotates past `max-wals` before a snapshot releases those files, the
  next restart fails with `failed to open WAL: wal: file not found` (#14252: 3.5.4 on Windows 10 and
  Server 2019; reproduced by a commenter with a single node, `max-wals: 5` and 200 KB writes, after
  3000-4000 transactions). Reproduction (Windows only, not run: no Windows host here; it
  cross-compiles at the pin with `GOOS=windows go test -c` and `go vet`):
  `issues/etcd-fileutil-windows-trylock-locked/lock_windows_trylock_test.go`, dropped into
  `client/pkg/fileutil/`, run from `client/pkg/` with `go test ./fileutil/ -run
  'TestTryLockFileOnLockedFile|TestPurgeFileKeepsLockedFile' -v`. Expected at the pin, by reading
  the code: both fail (`TryLockFile` returns a lock instead of `ErrLocked`; `purgeFile` removes a
  locked file). The existing `TestLockAndUnlock` (`lock_test.go:38`, `require.ErrorIs(t, err,
  ErrLocked)`) checks the same thing on every platform and should fail on Windows too; upstream CI
  does not run the unit tests on Windows.
- **Expected**: `TryLockFile` returns `ErrLocked` for a file another handle has locked, as on the
  other platforms (`lock_test.go:37-38`), so `purgeFile` stops at the first WAL file the WAL holds.
- **How the proof handles it**: outside the verified code. `client/pkg/fileutil` and
  `server/storage/wal` are not translated, and `lock_windows.go` is build-tagged `windows`. The
  server's `EtcdServer.purgeFile` is a trust-boundary axiom
  (`Proof/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__purgeFile.lean:24`) whose spec's
  postcondition is `True` (`Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__purgeFile.lean:26-30`),
  true of any behavior; the damage shows only at a restart, which the model does not include. A
  WAL/purger lock contract (`TryLockFile` returns `nil` → the caller holds the file's exclusive
  token) would make this an OS-level axiom checked per platform; it is false on Windows at the pin
  (`notes/bug-triage/etcd-14252.md`, proposal `wal-purge-lock-protocol`).
- **Possible fixes**: map `ERROR_LOCK_VIOLATION` to `ErrLocked` (compare the error value, not its
  text): `if errors.Is(err, windows.ERROR_LOCK_VIOLATION) { return ErrLocked }`, keeping `nil` only
  for `err == nil` (the shape of #14293). Run `client/pkg/fileutil`'s unit tests on Windows in CI.
- **Found**: 2026-10-16, bug triage of etcd-io/etcd#14252 (`notes/bug-triage/etcd-14252.md`).
