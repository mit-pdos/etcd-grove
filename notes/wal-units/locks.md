# Unit `locks`: file-lock semantics in `fsExt` (branch `wal-c-locks`, base `origin/wal-int`)

The user approved (2026-11-15) adding lock semantics to the trusted semantics (plan §5-§6 Q1, I5;
until now "deferred [user]"). This unit: the semantics, its evidence, its ghost state and WP specs,
the library specs over it (`fileutil.TryLockFile`/`LockFile`, `os.File.Close`), and their callers.
Using it in the WAL's purge reasoning is the next unit. Everything trusted here is **pending the
user's review** (as `notes/wal-fsext-models-review.md`'s drafts).

## 1. Why

etcd's WAL and its purger (`fileutil.purgeFile`, `--max-wals`) coordinate through file locks within
**one** process: the WAL holds a lock on each segment it may still read (`openWALFiles`'s
`TryLockFile`, released by `ReleaseLockTo`/`Close`), and the purger removes a segment only after
`TryLockFile` on a fresh fd succeeds. `fileutil` uses OFD locks (`F_OFD_SETLK[W]`) when the kernel
has them (its `init` probes `F_OFD_GETLK`), `flock(2)` otherwise; both are per **open file
description**, so two opens in one process conflict. Until now `Flock` and `OfdLock` returned any
errno and kept no state: nothing about locks could be proved.

## 2. Design

### 2.1 The state: a lock per description, in the description

An open file description is the model's `OsFd` (the value of an fd in `ProcState.fds`): no step
duplicates an fd (`dup`, `fork`, `SCM_RIGHTS` are not modelled, and Go's `os` never dups a regular
file's fd), so each fd is its own description. The locks a description holds are two new fields of
`OsFd`:

- `ofd : Option Bool` — its OFD (`fcntl`) lock on the whole file: `none`, `some false` (shared,
  `F_RDLCK`), `some true` (exclusive, `F_WRLCK`);
- `flk : Option Bool` — its `flock` lock: `none`, `some false` (`LOCK_SH`), `some true` (`LOCK_EX`).

Both default to `none`, which every `Open` gives. **The two kinds are independent** (measured: an
exclusive `flock` through one description and an exclusive OFD lock through another, on one file,
both succeed; `locks_flock_vs_ofd.go`): Linux keeps them on separate lists (`flc_flock`,
`flc_posix`) and checks each request against its own list only (`fs/locks.c`).

**Conflict** (`LockConflict st k fd i ex`): another fd (another description) of the same file holds a
lock of the same kind that conflicts with the request: an exclusive request conflicts with any lock,
a shared one with an exclusive lock. Whole-file locks only, so ranges never matter.

Since the locks live in the fd's entry, **`close` releases them** with no change to the `Close` step
(it deletes the entry; Linux releases a description's OFD and flock locks when its last fd closes,
`__fput` → `locks_remove_file`, run before `close(2)` returns to user space: the model's `Close`
step, as for the fd itself).
**A crash releases them** with no change either (the process's state is gone: `MachineCrash` makes
`proc` empty; locks are kernel memory, never on disk). `FsInit` starts with no fd, so no lock.

### 2.2 The calls

`OfdLock` now takes `(fd, (cmd, typ))`, `cmd` `F_OFD_SETLK` (37, non-blocking) or `F_OFD_SETLKW` (38,
blocking), `typ` `F_RDLCK` (0), `F_WRLCK` (1) or `F_UNLCK` (2). `Flock` takes `(fd, how)` as before,
`how` one of `LOCK_SH`, `LOCK_EX`, `LOCK_UN` (1, 2, 8), each with or without `LOCK_NB` (4). Both
share one rule, `LockStep st k fd d req nb`, for a request `req` (`some ex`: lock, exclusive iff
`ex`; `none`: unlock), non-blocking iff `nb`:

- **Lock** (`req = some ex`), only on a description with no lock of that kind (`d.lk k = none`;
  re-locking a description, a conversion included, is stuck: etcd never does it, and Linux's
  conversions are not atomic for `flock`):
  - success (errno 0): only when no conflict; the description gets the lock;
  - failure: any nonzero errno, **nothing changes**; `EAGAIN` (= `EWOULDBLOCK`) from a
    non-blocking request only when there is a conflict.
  - Non-blocking with a conflict: the model allows only the failures (`EAGAIN` or another errno).
  - **Blocking** (`F_OFD_SETLKW`, `flock` without `LOCK_NB`) is the same rule: success needs no
    conflict, so while another description holds a conflicting lock the call can only fail (any
    errno), never succeed: **it waits** (no step) or fails. Failure is allowed at any time; see 2.4.
- **Unlock** (`req = none`): success, the description's lock of that kind is gone (also with no
  lock: success, no change); failure: any errno, the lock gone or kept.
- **Access mode**: an OFD `F_WRLCK` needs a writable fd, `F_RDLCK` a readable one (Linux: `EBADF`,
  measured); the model makes the other case stuck (misuse, as a write on a read-only fd). `flock`
  needs no mode (measured: `LOCK_EX` on an `O_RDONLY` fd succeeds).
- **Stuck** (misuse, never reached by a proved program): another `how` (Linux: `EINVAL`, or for
  `LOCK_MAND` a success with no lock), another `cmd` or `typ`, re-locking.

### 2.3 The trusted models

- `syscall.Flock(fd, how)` (`LinuxFs/TrustedCode/syscall.lean`): unchanged body (one `Flock` step and
  `errnoErr`); the docstring now says what the step does.
- `syscall.FcntlFlock` and `unix.FcntlFlock`, for `F_OFD_SETLK`/`F_OFD_SETLKW`: load the seven
  fields of `*lk` (Linux copies the whole struct in, `do_fcntl`), and if `Whence = SEEK_SET`,
  `Start = 0`, `Len = 0`, `Pid = 0` and `Type` is one of the three, call `OfdLock (fd, (cmd, Type))`;
  otherwise panic (not modelled: a byte-range lock, which Linux accepts, measured; `l_pid ≠ 0`, which
  Linux refuses with `EINVAL`, measured). `*lk` is not written (`F_SETLK` copies nothing out).
- **`F_SETLK`/`F_SETLKW` (6, 7) are no longer the extension's `OfdLock`**: classic POSIX record
  locks belong to the process, so two opens in one process do not conflict and closing *any* fd of
  the file releases the process's lock (measured, `locks_posix_not_modelled.go`); the trivial model
  was sound only because it kept no state. Not modelled now: a panic. No program of the repository
  issues them (fileutil uses 37/38; walfs 37; minibolt `flock`).

### 2.4 What stays nondeterministic, and why

- **Every lock call may fail with any nonzero errno, with no change**: `ENOLCK` when
  `locks_alloc_lock` fails (`fcntl_setlk` allocates the request first; `flock` too), `ENOMEM` from
  the lock context's allocation, an LSM's `EACCES`/`EPERM` (`security_file_lock`), `EINTR` for a
  blocking call interrupted by a signal whose handler lacks `SA_RESTART`. None of these happens in
  the measured runs, and Go installs every handler with `SA_RESTART`, so a blocking call is
  restarted after a signal (measured: 20 `SIGUSR1`s with a Go handler, and the runtime's `SIGURG`s,
  never made a waiting `F_OFD_SETLKW` or `flock` return; `locks_blocking.go`). Only the allocation
  failures remain, and only "no allocation failure" (an environment assumption the model already
  makes for the write path) would remove them.
  **[user] option, not taken**: a blocking call that waits on a conflict returns only once the
  lock is free (no failure while conflicting), resting on `SA_RESTART` (measured) and on no
  allocation failure at the call's entry (assumed). It would make "the blocking `LockFile` on a
  held lock never returns" provable (the `Repair`-path hang); the model as drafted lets it return an
  error instead, which a partial-correctness proof handles as an ordinary error.
- **`EAGAIN` only on a conflict** (non-blocking): `posix_lock_inode` and `flock_lock_inode` return
  `-EAGAIN` only when they find a conflicting lock and the request may not sleep (`fs/locks.c`);
  measured for both kinds. Excluding it elsewhere is what makes fileutil's `ErrLocked` mean "held by
  another description".
- **A failed request changes nothing**: the kernel inserts the lock only on success (OFD:
  `posix_lock_inode`'s insertion is its last step, after every check and allocation; `flock`:
  `locks_insert_lock_ctx` after the conflict loop); with no lock of that kind on the description
  before (the lock rule's premise), there is none after.
- **An unlock may fail with the lock gone or kept** (an allocation at entry fails before; nothing
  after the removal can fail for a whole-file lock, but the model does not need to say so).

### 2.5 Ghost state and specs (untrusted, `GooseLang/Ext/Fs/Locks.lean`)

- A new ghost map `γlk : (LockKind × Ino) ↦ w64` in the extension's interpretation (`lockCtx`, a
  fourth part of `osCtx` beside `ofdCtx`): its authoritative map has `(k, i) ↦ fd` exactly when the fd
  `fd` holds an exclusive lock of kind `k` on the file `i` (`LockCoh`), and at most one description
  holds one when any holds an exclusive one (`LockWf`, which the semantics keeps).
- **The client's resource** `osLock k i fd`, the map's fragment, whole: an exclusive lock of kind
  `k` on `i`, held through `fd`. Two are exclusive: `osLock k i fd1 ∗ osLock k i fd2 ⊢ False`. So a
  successful non-blocking (or blocking) exclusive lock proves that no other description holds the
  lock (the purger's reasoning, next unit).
- `lockToks fd d`: the tokens of the exclusive locks `d` holds (`emp` for an unlocked `d`, which
  every `openFd` is).
- Specs: an exclusive lock (`wp_osOfdLockEx`, `wp_osFlockEx`): `osFd fd 1 d` with no lock of the
  kind → on success `osFd fd 1 (d.setLk k (some true)) ∗ osLock k d.ino fd`, on failure `osFd fd 1
  d`; a shared lock (no token); an unlock (gives back the token, or keeps it on a failure that kept
  the lock); `Close` (`wp_osClose`): now takes `lockToks fd d` with `osFd fd 1 d` (`emp` for an
  unlocked description, so every existing caller is unchanged but for the premise).
- Every other step keeps `lockCtx` (its existing fds keep their descriptions; a new fd is unlocked);
  the liftings (`wp_os_step`, `wp_fs_stepT`, `wp_fs_stepM`, the tree's) apply that generic lemma, and
  the lock calls and `Close` use a lifting that hands `lockCtx` to their proof.

### 2.6 Library specs (`LinuxFs/`)

- `os.File.Close.spec`: with `lockToks fd d` (the description's tokens, released).
- `fileutil.TryLockFile`/`LockFile`: `lockPost` gives, on success, the open's resources with the fd
  locked: `osFd fd 1 ((openFd i fl).setLk k (some true)) ∗ osLock k i fd`, for the lock kind `k` the
  package's initializer chose (`fileutil.lockKind k`, persistent, from `isPkgInit`: OFD or `flock`,
  the same for every call, so the WAL's and the purger's locks are of one kind); on an error, as
  before (the file it opened is closed, unlocked). `TryLockFile`'s `ErrLocked` additionally means a
  conflict (not used yet).
- The callers (`openWALFiles`, `createNewWALFile`, the pipeline, `Create`, `Repair`, walfs's
  `SegLog`, minibolt's `flock`) carry the token with the fd and give it back at `Close`; the
  client-facing WAL specs do not change in this unit.

## 3. Evidence

`examples/osfs/semantics/locks_*.go` (one decision each, indexed in `doc.go`), measured by
`locks_test.go` on configuration C (`run-models-on-c.sh -run TestLocks`, 2026-11-15, Linux
7.0.0-1014-aws, a fresh ext4 loop mount that `check.sh` reports as C): all eight tests pass.

## 4. Log

(below, per session)
