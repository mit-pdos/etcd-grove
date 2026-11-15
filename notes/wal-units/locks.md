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

## 4. Pending the user's review (the trusted change, in `notes/wal-fsext-models-review.md`'s style)

Scope: `GooseLang/Ext/Fs/Impl.lean` (`OsFd.ofd`/`flk`, `LockKind`, `OsFd.lk`/`setLk`, `OsState.setFd`,
`LockConflict`, `LockStep`, `flockReq`, `ofdReq`, `EAGAIN`, `F_OFD_SETLK[W]`, the `Flock` and `OfdLock`
cases of `IsFsStep`, the header's **Locks** paragraph; `Open` builds its description with
`OsFd.mk ... none none`), `LinuxFs/TrustedCode/syscall.lean` (`Flock.impl`'s docstring;
`FcntlFlock.impl`: 37/38 read the description and pass its type, 6/7 panic) and
`LinuxFs/TrustedCode/golang_org/x/sys/unix.lean` (`model.Flock_t`, `FcntlFlock.impl`, same). Go
examples: `examples/osfs/semantics/locks_*.go` (indexed in `doc.go`), measured by `locks_test.go` on C.
`Close`, `MachineCrash` and `FsInit` are unchanged: the locks are fields of the description.

What to check:
1. **Blocking requests may fail at any time** (any errno, no change), including while waiting: kept
   because `ENOLCK`/`ENOMEM` at the call's entry cannot be excluded without an allocation assumption.
   The [user] alternative (no failure while a conflicting lock is held, resting on `SA_RESTART`,
   measured, and on no allocation failure at entry, assumed) would make a `LockFile` on a held lock
   never return (the `Repair`-path hang); not taken.
2. **`EAGAIN` only on a conflict, and only for a non-blocking request** (`LockStep`'s failure
   premise `nb = true → e = EAGAIN → LockConflict`). Source: `posix_lock_inode`/`flock_lock_inode`;
   measured.
3. **Stuck cases** (misuse): re-locking a description (Linux accepts, `TestLocksOFDSameDescription`),
   `F_WRLCK` on a non-writable fd and `F_RDLCK` on a non-readable one (Linux `EBADF`), another `how`
   (Linux `EINVAL`, `LOCK_MAND` success), another `cmd`/`typ`. Panics in the models: byte ranges,
   `l_pid ≠ 0`, `F_SETLK[W]`.
4. **flock and OFD independent** on C (measured); NFS-like filesystems are outside C.
5. **No `dup`**: each fd is its own description. True of every step; Go's `os` never dups a regular
   file's fd.
6. The model loads `Type`, `Whence`, `Start`, `Len`, `Pid` of `*lk` (not the padding): a concurrent
   write of those fields is a race a proof must exclude (Linux copies the struct in).

## 5. Log

### Session 1 (2026-11-15)

**Done** (branch `wal-c-locks`):
- Design (§2), evidence (§3: `locks_*.go`, `locks_test.go`, all 8 tests pass on C), the semantics and
  the trusted models (§4), committed `3ae8215f47`.
- Ghost state and ext specs (untrusted): `lockCtx` (a fourth part of `osCtx`, ghost map `γlk`),
  `LockWf`/`LockCoh`, `LockFrame` and `isFsStep_lockFrame` (every step but the lock calls and `Close`
  keeps the locks' interpretation; the liftings `wp_os_step`, `wp_os_stepX`, `wp_fs_stepT`,
  `wp_fs_stepM`, `wp_fs_stepTC`, `wp_fs_stepO` take `¬ LockOp o` with a default proof), `wp_os_stepL`
  (the lifting of the lock calls and `Close`), `GooseLang/Ext/Fs/Locks.lean`: `osLock k i fd`
  (exclusive: `osLock_excl`), `lockTok`, `lockToks`, `lockOut`, `wp_osLockStep`, `wp_osOfdLock`,
  `wp_osFlock`, `wp_osClose` (now takes `lockToks fd d`; `emp` for an unlocked description,
  `lockToks_unlocked`). `CommitMono.lean`: `lockStep_cases`, `lockStep_val`, `setLk_ino` etc. All of
  `GooseLang/Ext/Fs` builds (1543 jobs, after merging `origin/wal-int`).
- LinuxFs specs: `syscall.Flock.spec` (the lock rule, `lockOut`), `syscall.FcntlFlock.wp_lock` and
  `unix.FcntlFlock.wp_lock` (whole-file description, `lockOut`), `os.File.Close.spec` (takes
  `lockToks fd d`). `fileutil`: `lockPost`'s success now gives `osFd fd 1 (fileutil.lkFd k i flag) ∗
  osLock k i fd ∗ fileutil.lockKind k` (`k` the kind the package's initializer chose, persistent);
  `TryLockFile.spec`/`LockFile.spec` take `flag`'s write mode (`decide (... % 4 ≠ O_RDONLY) = true`;
  `F_WRLCK` needs it); `fileutil.lockOut_split`. The package fact `fileutilInit` now records
  `wrlck.Pid' = 0` (`etc/gen-init.py` updated, `Init.lean` regenerated, `--check` clean).
- Clients repaired: the `os` proofs (`File.Close`, `StatS`, `RemoveAllLeaf`, `WriteFile*`, `CrashFile`'s
  `fsStep_val`), `durable`, `crashlog`, `walfs` (`SegLog.wp_lockFile`: the OFD lock's real outcome; the
  token goes to `Segment`'s closes), minibolt (`flock.spec`: the real outcome; `DB.close.spec(Crash)`
  take `lockToks`; the `flock` token is kept with `rwR`'s half of `cls`, `clsOpen`, and given back at
  `DB.Close`; the database's fd description is `⟨γ.ino, true, true, none, some true⟩`). All their
  leaves build (`bboltfs` Link/Results, `walfs`/`crashlog` Results, `durable` Link, fileutil).

**Not done: the WAL** (`LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/`) does not build: its
proofs store descriptions as 3-field literals and `openFd` values and close locked files without
tokens. The failures at its base (after the merge): `Handle.lean:405` (`∃ rd, osFd fd 1 ⟨i, rd,
true⟩`), `closeAll.lean` (`rcFile`'s `Close` without `lockToks`), `PipeLemmas.lean` (`lockPost`'s new
shape). Everything importing them is not yet checked. Plan for the repair (the next session):
1. **Tail descriptions** (`walTailW`, `HandlePend` 107/120, `RepairTailDefs` 48, `TailWriterW` 836,
   `WAL__sync` 257, `WAL__Close` 144, `WAL__CloseU` 153): `∃ (rd : Bool) (lo lf : Option Bool),
   osFd fd 1 ⟨i, rd, true, lo, lf⟩ ∗ lockToks fd ⟨i, rd, true, lo, lf⟩`; uses `⟨i, rd, true⟩` →
   `⟨i, rd, true, lo, lf⟩`, patterns `⟨%rd, Hfd⟩` → `⟨%rd, %lo, %lf, Hfd, Hlt⟩`; the closes give `Hlt`.
2. **Generic closables** (`CloseDefs.rcFile`, `walClosable`, the locks list at CloseDefs:43): add
   `lockToks fd d`; `closeAll`, `openWALFiles` (`walOpenedRc_rcFile`, `walRcLink_rcFile`),
   `VseAttemptLemmas` carry it.
3. **Locked segment files** (`walOpenedRc`/`walOpenedFile` in write mode, `ReadDefs` 76/86, `Pipe.pipeFile`,
   `OpenLastDefs` 47, `Create`'s files): the description `fileutil.lkFd k i flag` (write mode) and
   the token; a small lemma `lkFd k i fl = ⟨i, rd, wr, lo, lf⟩` (by `cases k`) lets the tail form of 1
   absorb them (cut makes the pipeline's file the tail). Read-mode files stay `openFd` (no lock).
4. `Repair`'s blocking `LockFile`: `lockPost` as above (it may return an error while the lock is held:
   §2.4's option not taken).
The client-facing WAL specs need not change: the tokens and descriptions are internal to the handle's
predicates.

**Next unit (purger, `ReleaseLockTo`, `Repair` path, `purgeRound`)**: with the WAL repaired, the WAL's
invariant keeps, for each segment it may still read, the token `osLock k i fd` of the package's kind
(`fileutil.lockKind k`); `ReleaseLockTo`'s closes give the tokens back to the ghost (released); the
purger's `TryLockFile` success gives `osLock k i fd'`, and `osLock_excl` with the WAL's token shows the
WAL no longer holds segment `i` (the kinds agree: both from `fileutil.lockKind`, whose agreement law
`lockKind k1 ∗ lockKind k2 ⊢ ⌜k1 = k2⌝` still needs `functions` injectivity on the two names, or a
restatement of `lockKind` by the stored function's identity). `purgeRound` then removes it under
that knowledge. `Repair`'s `LockFile` on a lock the boot path left held: with §2.4's model it returns
an error or waits; a proof of the hang would need the [user] option.

**Decisions left for the user**: the whole trusted change (§4); §2.4's blocking option. **No new
axiom**, no `sorry`. **No Go bug found.**

### Session 2 (2026-11-15)

**1. The WAL repaired** (builds: the WAL `Link`, the tester's `Link`/`Main`/`Boot`, `durable`'s `Link`, after
merging `origin/wal-int` at `ba70ab7e55`):
- `LockLemmas.lean` (new): `fdKindOk d` (each exclusive lock `d` holds is of `fileutil`'s kind, persistent),
  `fdLocks fd d := lockToks fd d ∗ fdKindOk d` (what every WAL file predicate holds with `osFd fd 1 d`),
  `fdLocks_unlocked`/`fdLocks_openFd`/`fdLocks_toks`, `lkFd_eta`/`lkFd_ino`/`lkFd_lk`/`lkFd_toks`/`lkFd_locks`,
  `lkFd_open` (a `LockFile`/`TryLockFile` success as a literal description with its `fdLocks`).
- Descriptions as literals, not `lkFd` (whose projections are stuck on the kind): the tail
  `∃ rd lo lk, osFd fd 1 ⟨i, rd, true, lo, lk⟩ ∗ fdLocks fd ⟨…⟩`; `openWALFiles`' segments `walSegFd write lo lk i
  := ⟨i, true, write, lo, lk⟩` (read mode unlocked); `pipeFile`, `wp_createTmp`, `wp_createSeg`, `walLastOpen`
  as `⟨i, _, true, lo, lk⟩` with `fdLocks`. `walFileS`, `wal.rcFile`, `walClosable`, `walLockH`, `walTieFile`,
  `walFileAt` carry `fdLocks`. Every `Close` of a WAL file passes `fdLocks_toks`. The internal callee specs that
  name such files changed with them (ledger, 2026-11-15, "the WAL's internal file predicates"); no client-facing
  WAL spec changed.

**2. The law** (`LinuxFs/Proof/.../fileutil/LockKind.lean`): `fileutil.lockKind_agree : lockKind k1 ∗ lockKind
k2 ⊢ ⌜k1 = k2⌝`, proved: the persistent points-tos agree, and `fileutil.lockFn_inj` (the two lock functions'
values differ: `FuncUnfold` makes each value its body, and `simp` separates the bodies). No restatement needed.

**3. The purger** (partial): `fdLocks_excl` (`LockLemmas.lean`): `fdLocks fd d ∗ osLock k' d.ino fd' ∗
lockKind k' ⊢ False` when `d.lk k = some true`: whoever gets a segment's lock (of `fileutil`'s kind) knows no
locked WAL file description is on it. **Not done**: the WAL-level statement (the handle's locked segments
exposed, `ReleaseLockTo`'s `unl` tied to them) and `ReleaseLockTo`'s re-proof. What it needs: `walLockH` (and
the tail) record the segment's inode and that the description is locked (`walSegFd true lo lk` with
`lo = some true ∨ lk = some true`, kept from `lkFd_open`), the handle's predicate the segments from `unl` on
as those inodes, and a law on the sealed `walOpenWF` (`walOpenWF ∗ osLock k' i fd' ∗ lockKind k' ⊢ ⌜i` not a
segment the handle still needs`⌝`); `ReleaseLockTo` then re-proved with `unl` meaning "every record from there
on is in a file whose lock the handle holds".

**4. `purgeRound`: not restored.** Its Go is in `bb9a9866b6^:examples/etcd/wal/wal.go`. Restoring the call in
`opOwnSnap` without a proof of `purgeRound` would put an unproved function under the tester's closed result.
The proof needs more than item 3's law: `purgeRound` opens (`TryLockFile`) and removes (`os.Remove`) segment
files in the WAL directory while the handle is open, but the directory's name claim is split between the
handle and `walInv` (`walDirKey`, `osNames` halves) and the invariant has no law letting a third party open or
remove a segment name, nor a ghost step raising `pur`/moving `cut` over `fsExt` (`walPurge_step` in
`WalDisk.lean` is over the main tree's absDisk extension). That law (a purge right `walPurgeW` over `fsExt`:
the claim on a segment name below `unl` lent to whoever holds its lock, the removal recorded as `pur := max pur
unl`) is the next unit, with item 3's WAL-level statement.

**5. The boot path** (the user's decision, 2026-11-15: the lock model as it is; `notes/decisions.md`, "fsExt:
file locks per open file description"): proved over the current model, both outcomes:
- `fileutil.lockPost_held` (`LockKind.lean`): with `osLock k i fd ∗ lockKind k` held, `LockFile`/`TryLockFile`'s
  post on a file at `i` has no success arm (an error, the open's resources, the held lock kept). A blocking
  call that never returns satisfies any post (partial correctness).
- `openLast.specHeld` (spec in `Spec/.../openLast.lean`, proof `openLastHeld.lean`): with the directory claim's
  share the failed handle holds (path, `osNames j (.except X)` at the layout's names, the last segment `gL`)
  and `gL`'s held lock: only an error, nothing changed.
- `wal.Repair.specHeld` (spec in `Spec/.../Repair.lean`, proof `RepairHeld.lean`): `false`, nothing changed.
- **What is left for the caller**: `WAL.Close.specFailed`'s error arm must give those resources (ledger,
  2026-11-15, "`WAL.Close.specFailed`'s error arm for the boot path's `Repair`"); `Close.specFailed` is itself
  unproved (`walReadFailedF` a stub), and `openWALFromSnapshot` is not translated in the part. The error path
  of `Repair` goes through; nothing in it needed an assumption.

**Decisions left for the user**: the trusted change's text (§4); the proposed `Close.specFailed` strengthening.
**No new axiom, no `sorry`. No Go bug found.**

### Session 3 (2026-11-15, branch `wal-c-locks3`, base `origin/wal-int` `7fe119fb19`)

**Done** (all built with `lake build`: the WAL `Link`, the tester's `Link`, `CloseFailedRepair`; no new axiom, no
`sorry`, nothing trusted changed, no Go changed):

- **Item 6, the links.** `openLast.specHeld` and `Repair.specHeld` are linked in the WAL `Link.lean`
  (`wp_openLastHeld`, `wp_RepairHeld`, both pending on `errors.IsPathErrnoTerm`/`fmt.ErrorfErrsTerm` like
  `wp_Repair`). The laws are linked too: `etc/link_walfs.py` gains `LAWS` (`WALFS_LAWS`: `fileutil.lockKind_agree`,
  `fileutil.lockPost_held`, `fdLocks_excl`), emitted in a `section laws` as `law_<name>`, each restated from its
  declaration and applied to its explicit binders (so they are roots of `etc/tcb-report.py`). The tester's `Link`
  was stale at the base (its `NoIoErr` section variables since the noioerr merge): regenerated, builds.
  `etc/tcb-collections/linuxfs.txt` not rerun (needs a full build of the roots): for the coordinator.
- **Item 5, the statement and the boot-path composition** (ledger, "`WAL.Close.specFailed`'s error arm for the boot
  path's `Repair`", P7 continued: **Made**). `WAL.Close.specFailed`'s post is now `(walUnlockedTok ∗ osCallPerm ½) ∨
  (⌜err ≠ nil⌝ ∗ walCloseLeft R dir)`. `walCloseLeft R dir` (`CloseLeft.lean`): `osSharedInv R`, a path to `dir`,
  the handle's half `osNames j (.except X) ½ hj` with exactly `Repair.specHeld`'s layout facts (`CloseLeftOk`), the
  last segment's `osLock k gL.ino fd ∗ fileutil.lockKind k`, the call permission's half (the handle's quarter and the
  closed pipeline's). **`wal.Repair.wp_afterCloseFailed`** (`CloseFailedRepair.lean`, proved over
  `Repair.specHeld`): with `walCloseLeft R dir` and the client's half of the call permission, `Repair(lg, dir)`
  returns `false` and both come back (etcd's `openWALFromSnapshot` path). The tester's `restartRead` drops the new
  resources (its error branch fails the read). Not linked (an entailment with a spec hypothesis; `LAWS` would leave
  `Repair.specHeld` a hypothesis rather than `wp_RepairHeld`).

**Not done: `Close.specFailed`'s proof and `walReadFailedF`'s body** (item 5's rest). The plan of the W4c U5 log
(fifth session, "What is left for `Close.wp_proofFailed`") stands: `walReadFailedF` a disjunction of the pending
form (E1-E5), the `walTailP … TailMetaZ` form (E7), the `walTailW … TailMetaS` form (E8-E10, the key) and the
`walTailPE` form (E6); the ten `readAll_failWpQ` sites of `WAL__ReadAll.lean` supply it in place of `lg`/`dir`;
`Close.wp_proofFailed` puts the tail back (`walInvBody_untailL`, `walInvBody_untail`) and unpins the segments. The
error arm now additionally needs, at `w.sync()`'s failure, the claim's half and the layout facts (`CloseLeftOk`,
from `WalAbsD.names`/`seqName` at the last look at the invariant, which the claim's half keeps true: the claim
changes only with both halves) and the last segment's token (the tail's `fdLocks`, `lkFd_toks`). **E6 needs a new
invariant step** (`syncLayP`, the fdatasync of a lent tail with a torn frame past `wr`: the U5 log's last item);
it is the one piece of new invariant work.

**Not done: items 1-4 (the purge).** Reading the invariant shows they are one invariant change, larger than one
session; the design, for the next session:

1. **What the tie needs.** A purge removes the first named segment (`lay.first`): `WalAbsD.cut` (`d.cut =
   segStart lay.cuts lay.first`, `0 < first → d.cut ≤ d.pur`) then needs `segStart lay.cuts (first + 1) ≤ max pur
   unl`, i.e. the removed segment holds no record from `unl` on. That is a fact about the **handle's** locks (its
   `walLockH` list and the tail) **against the invariant's** layout and `d.unl`, so it must live in `walInv`: no
   existing ghost carries it (`walTailsRes`' record pins `(H, md, cuts, wr, ino, fl)`, not the locked segments;
   `absLe`/`walPast` do not track `unl`; the handle's claim half pins the directory's names, not `unl`).
2. **Proposed ghost.** A new `WalGS` field `γlk`, a ghost map `dir ↦ inos : List Ino` (the inodes the open handle of
   `dir` keeps locked, the tail last): its authority in `walInv` (one allocation site, `Ghost.lean`), the element in
   `walHandleIn` (with `walLockH lf i` recording `d.ino = i ∧ ∃ k, d.lk k = some true`, the tail likewise: both are
   `LockFile`/`TryLockFile` successes, `lkFd_lk`). The invariant's pure fact per registered `dir` (`LksOk d lay
   inos`): `inos = (lay.segs.drop (|segs| - |inos|)).map ino`, `inos ≠ []`, and `|inos| < |segs| → segStart
   lay.cuts (first + |segs| - |inos|) ≤ d.unl`. Placement: inside `walTailsRes`' per-directory entry, beside
   `TailBound` (every site rebuilding the entry already re-proves `TailBound`; the fact depends only on `d.unl`,
   `lay.first`, `lay.cuts`, the segments' inodes). Cost: the 27 `walTailsRes` unfold sites (21 files), the handle's
   30 files (most frame it), and the steps that move it: `Open`/`ReadAll` (register: `inos` the opened segments,
   `unl` raised to `walOpenPos` by `walInv_unlAU`'s sibling `OpenUnl`), `cut` (append the new tail's inode),
   `ReleaseLockTo` (raise `unl` at its commit, then drop locks while `segStart` stays `≤ unl`: the name argument is
   `WalAbsD.nameBound` with `walReleasePos`'s `walNameBound`, the guard part from `walGuardPos`), `Close`
   (unregister), crash (dropped with the contents).
3. **Item 1's law** then reads: `walInvBody s ∗ walHandleIn … ∗ osLock k' i fd' ∗ fileutil.lockKind k'` and `i` the
   inode of segment `q` of `dir`'s layout `⊢ ⌜segStart lay.cuts (q + 1) ≤ d.unl⌝` (by `fdLocks_excl` against the
   handle's lock on `i`, then `LksOk`). Sealed form over `walOpenWF`: an update opening `walInv`.
4. **Item 2, the purge right**, beyond the tie: (a) the name: the handle holds half of the directory claim
   (`walDirH`), so the removal (which needs the whole claim) takes `walOpenWF` (the tester's case: `purgeRound` runs
   in the handle's thread) and splits `(j, .except X)` into the name's `(j, .only [nm])` and the rest
   (`NameSplit.lean`); a third-party purger (the server's goroutine) would need the tokens in `walInv` instead
   (a [user]-free internal choice, deferred: the tester needs only the first). (b) Crash: the removal is not
   durable until the directory's fsync, so a crash may bring the segment back: `CrashTo` needs the pre-purge layout
   as an alternative, and `CrashOkW` has **one** `alt` (the pending cut's); a purge between a cut's rename and its
   directory sync needs two, so `alt : Option WalLay` becomes a list (or the purge waits for `walCutAuth none`). The
   purged inode's halves (`segResP`, the invariant's half) stay in `walInv` until the directory is durable (its
   `FileCrashedR` premise). (c) The `fsExt` counterpart of `walPurge_step`: `pur := max pur unl`, `first + 1`,
   `cut := segStart (first + 1)`, given (3).
5. **Items 3-4** follow: `ReleaseLockTo` over (2) (its closes take the tokens back from `fdLocks`, unchanged, and the
   tie's update); `purgeRound` restored (Go `bb9a9866b6^:examples/etcd/wal/wal.go`, its call in `opOwnSnap`),
   `fileutil.ReadDir` of the WAL directory under the handle's claim half, then per name `TryLockFile` (success: the
   law of (3); `ErrLocked`/any error: return), `os.Remove` by the right of (4), `l.Close()` with the token.

**Coordination.** `wal-c-noioerr3` (`21a3d42167`, not yet in `wal-int`) changes `walLockH` (an optional name
predicate, `walSegName`): the tie of (2) should be built on that form after it lands in `wal-int`.

**Decisions left for the user**: none new (the trusted change's text, §4, still pending review).
**No new axiom, no `sorry`. No Go bug found.**

### Session 4 (2026-11-15, branch `wal-c-purge`, base `origin/wal-int` `f2ee139e77`)

**Done** (built with `lake build`: the WAL `Link`, the tester's `Link`, `durable`'s `Link`, `PurgePure`; no new
axiom, no `sorry`, nothing trusted changed, no Go changed, no spec statement changed):

- **Item 1, the tie's invariant half** (a cheaper placement than session 3's): not a map in `walTailsRes`'s
  per-directory entries (27 unfold sites) but a new ghost variable `WalGS.γlk` of a map `Lk : dir ↦ b` (a
  history position), **half in `walGhost s`** (`walLksAuth s`, with `LksOk s Lk`: each `b` is at most
  `dir`'s `unl`), **half the lock holder's** inside `walTailsFrag T Lk` (a new second argument, default `∅`,
  so the lock token's `walTailsFrag ∅` says no range is registered and every existing use is unchanged).
  The invariant fact needs no layout: what ties `b` to the segments is the handle's (below), since the handle
  already pins the cuts (its tail record) and the directory's names and inodes (its half of the claim, `hj`,
  with `WalAbsD.names`/`seqName`), so only `unl` (the invariant's, raised by client updates) needs a ghost.
  `unl` only rises within a generation (`max` raises; a crash starts new ghost state), so the only cost is a
  premise `UnlMono s s'` on `walGhost_updR`/`walGhost_upd`/`walGhost_upd_lag` (5 callers: `unlMono_upd`,
  `unlMono_insert`) and the three sync steps that rebuild `walGhost` by hand (`TailSync`, `TailSyncPend`,
  `RepairSync`). Laws: `walLks_agree` (the halves agree; `LksOk`), `walLks_set` (both halves set to any `Lk'`
  with `LksOk s Lk'`: a handle registering, raising or dropping its range), `walLksAuth_mono`.
- **Item 2, the layout step** (`PurgePure.lean`): `walAbsD_purge`: removing the first named segment's name
  (not the last) takes `WalAbsD d lay ents` to `WalAbsD (walPurgeD d lay p) (purgeLay lay) ents'`
  (`first + 1`, the segments' tail; `pur := max pur p`, `cut := segStart cuts (first + 1)`), given
  `segStart lay.cuts (lay.first + 1) ≤ p`, the directory's `.wal` entries being the rest. Not yet used.

**The crash issue, settled (design; not implemented).** `purgeRound`'s Go (`bb9a9866b6^:examples/etcd/wal/wal.go`)
removes with `os.Remove` and **never fsyncs the directory**; the next durable point is the next `cut`'s
`w.dirFile` sync (or `Create`'s). In `fsExt` a crash keeps a `Follows`-closed set of the logged metadata
operations (`Tree.lean`), and the round's removes are sequential in one thread (each call begins after the
previous returned), so a crash keeps a **prefix** of the removes, and a later cut's rename survives only with
all of them: the possible layouts form a chain (no holes, unlike the old abstract disk's out-of-order unlinks,
`nonissues/etcd-wal-purge-unlink-gap.md`). Chosen: the invariant keeps, per directory, the removed-not-durable
segments `pg : List SegG` (contiguous, just before `first`, their invariant halves parked until the directory
is durable, `FileCrashedR` premise), and `CrashOkA`'s alternatives become "`lay`, or the pending cut's `alt`
(or `lay`), with a suffix of `pg` put back in front" (a list of alternative layouts, structured). The other
option, "the purge waits for a directory sync", is not available without a Go change (`purgeRound` has no
directory fsync), so not taken. The abstract state needs nothing new: a crash re-chooses `cut ≤ pur`, and the
purge raised `pur` to at least the removed segments' end before removing anything.

**Not done: the handle's half of the tie, items 2 (the law), 3, 4.** What is left, in order:

1. **The handle's relation** (the next step; a `walHandleIn` restructure). The handle must hold its half
   `walTailsFrag {dir ↦ γt} {dir ↦ b}` (in `walDirH`, today `walTailsFrag {dir ↦ γt}` with `Lk = ∅`) and the
   fact the purge law needs: every `.wal` name of `hj` whose inode no handle lock holds has
   `segStart h.cuts (seq + 1) ≤ b`, and each lock's description is on the inode `hj` maps its base name to,
   exclusively locked (`∃ k, d.lk k = some true`, from `lkFd_lk` at `openWALFiles`). The obstacle: `hj` is
   private to `walDirH`, the lock list to `walHandleIn`, the cuts to the tail record; no single predicate
   sees all three. Least churn found: give `walDirH` the non-tail lock list and the cuts as parameters
   (`walHandleIn` passes `lfs.dropLast`, `h.cuts`) and move the `walLockH` bigsep into it (its conjunct in
   `walHandleIn` becomes `True`, so the 53 `walHandleIn` patterns keep their positions); `walLockH lf` gains
   `(nm, i)` facts (its base name and description inode). Sites: `walDirH`'s 11 unfolds (17 files),
   `walLockH`'s 12 files, then the steps: `Create` (register `b = 0`), `ReadAll`/`Open` (register `b` = the
   raised `walOpenPos`; the unselected names end before it), `cut` (the new name is the new tail's; cuts
   appended keep `segStart` of the old names), `ReleaseLockTo` (item 3: `walLks_set` to `walReleasePos H a`
   right after its `unl` commit; each closed lock's segment ends before it, by `WalAbsD.nameBound`), `Close`
   (`walLks_set` to `∅` before `walTails_unregister`).
2. **The purge law** (item 2): at `os.Remove(dir/nm)`'s step (`os.Remove.specFileSnc`, the claim `.only [nm]`
   split from both halves of `(j, .except X)`, `NameSplit.lean`), with the remover's `osLock k i fd'` and
   `lockKind k`: `fdLocks_excl` against every handle lock gives `i` unlocked by the handle, so the
   relation gives `segStart cuts (seq nm + 1) ≤ b ≤ d.unl` (`walLks_agree`); `nm` is the first named
   segment (the round removes oldest first; the handle's thread is the only one changing names) and not the
   last (the tail is locked); `walAbsD_purge` with `p = d.unl`; the removed segment into `pg` (above).
   **The client's state moves at each removal** (`WalAbsD.cut` fixes `d.cut = segStart lay.cuts lay.first`),
   so `purgeRound` cannot take one atomic update (the old main-tree axiom committed once with a prophesied
   outcome). Proposed spec shape: a predicate `Pc` of the caller and a persistent, repeatable commit
   `□ ∀ d, Pc d -∗ AU-like access to walDiskAt dir d giving walDiskAt dir (walPurgeD …) ∗ Pc (…)`, which
   the tester supplies from `TInv` (`tCandOk` needs `d.pur, d.cut ≤ c.pur`). Alternative (changes
   `ReadAll`'s client-facing reading of `d.cut`): relax `WalAbsD.cut` to a range. Recommended: the first.
3. **A point to check before item 4** (possible tester-oracle mismatch, not a WAL bug): the Go raises each
   candidate's `pur` to its `unl` before `purgeRound`, but `tCandOk` bounds `d.unl` by `max c.unl
   (tOpensBound o c)`; if `d.unl` can exceed `c.unl` at `opOwnSnap` (an `Open` that raised it past the
   oracle's `unl`), a purge to `d.unl` may go past `c.pur`. The restored proof needs `d.unl ≤ c.pur` there
   (or the purge's `p` the oracle's bound); check `resume`/`restartRead`'s raise of `c.unl` first.
4. **`purgeRound` restored** (item 4) only once 1-2 are proved: restoring the call in `opOwnSnap` without a
   proof would put an unproved function under the tester's closed result (session 2). Not done; Go untouched.

**Decisions left for the user**: none new (the trusted change's text, §4, still pending). **No new axiom, no
`sorry`. No Go bug found** (item 3 above is a check on our own tester, not a finding).

### Session 5 (2026-11-15, branch `wal-c-purge2`, base `origin/wal-int` `dbd4495eb5`; merged `32d1f57a80`, synclent)

**Done** (built with `lake build`: the WAL `Link`, the tester's `Link` and `Main`; no new axiom, no `sorry`, nothing
trusted changed, no Go changed):

- **Item 1, the handle's half of the tie** (`Handle.lean`, `LockRange.lean`). As session 4 planned, with the
  least churn: `walDirH dir j dfd ino name k lfs cuts …` takes the non-tail lock list and the cuts, its old
  `walTailsFrag` conjunct is now `walDirLks dir hj nm0 lfs cuts` (one conjunct, so every `walDirH` pattern keeps
  its shape): the holder's half `walTailsFrag {dir ↦ γt} {dir ↦ b}`, the non-tail locks `[∗list] lf; l ∈ lfs; ls,
  walLockHI lf l.1 l.2` (a lock on the segment named `l.1` with inode `l.2`, exclusively locked: `walLockH` plus
  `d.ino = i ∧ ∃ k, d.lk k = some true`) and `LkRel hj cuts nm0 ls b`: the locked segments are the last ones by
  sequence (tail `|cuts|`, the non-tail ones the `|ls|` before it, each at its name in `hj`), every other `.wal`
  name has a smaller sequence, the first locked segment starts at or before `b`, `|cuts| < 2^64`. The lock slot
  of `walHandleIn` (and `walHandleC`) is `True`. The tail's description is now known locked: `walTailW` holds
  `fdLocksW` (so `cut` can make the old tail a `walLockHI`); `walLockIn`/`wp_createSeg` carry it for `Create`.
  The range moves:
  - `Create`: registered at 0 in its commit (`walTailReg`, `CreateAu.lean`, `walGhost_lksSet`).
  - `ReadAll`: registered at the first read segment's start in its registration look (`walInv_readCommitReg`
    takes `hPre`); `LkRel_read`. **This needed a client-facing premise** (ledger 2026-11-15, "the handle's half of
    the lock tie"): `ReadAll.spec`'s atomic precondition now also says `walOpenPos (d.H) s.1 ≤ d.unl`, what
    `Open(s)`'s update left (nothing the proof holds between `Open` and `ReadAll` records it: `unl` is not in
    `absLe`, and nothing freezes the history before the tail is registered). The tester gives it from
    `walOpenRaise` (`restartRead.lean`). With it, `absD_segStart_le_openPos` (over `cutStart_le_openPos`,
    `ReleasePos.lean`: no snapshot record after the segment needed) bounds the start. The read path's failure laws
    (`walInv_untailPend`/`Key`, `readAll_failPend`/`Synced`, `walInv_readGive`, `walTailsRes_only`) take any
    range and drop it; the lent exits use `readAll_failWpQL` (drops it at the failed-opening step).
  - `cut`: `walDirLks_cut` (`LkRel_cut`; the old tail's lock `walLockHI_ofTail`).
  - `ReleaseLockTo`: below. `Close` (all three) drop it before the unregistration (`walInv_lksDrop`,
    `ReleaseAu.lean`).
- **Item 3, `WAL.ReleaseLockTo.wp_proofNoErr`/`wp_proof` re-proved over the tie** (statements unchanged). The commit
  (`walInv_releaseLks`, `ReleaseTie.lean`) raises `unl` and the range together, to `b' = max b (walReleasePos H
  a)`, and returns, from the layout (`walInvBody_handleLook`: the claim's names against `WalAbsD`, the tail record's
  cuts and history), that every `.wal` name of the directory with index below `a` starts at or before `b'`
  (`absD_name_le_releasePos`, over `cutStart_le_releasePos`; `walFileName_inj`). The name loop now records that
  every lock before the counter has index below `a` (the names from `LkRel_names`, persistent `walLockBase`), so the
  kept lock `smaller` has; `LkRel_release` drops the first `smaller` locks (`walLocksHI_split`). `durable`'s `Link`
  not rebuilt (no change in what it uses, not checked).
- **Item 4, the tester's oracle covers a purge: yes, no mismatch.** Session 4's worry (an `Open` raising `d.unl`
  past `c.unl`) does not arise at `opOwnSnap`: the running member's relation is `tMemOk o c d`
  (`Member.lean`), which has `o.opens = []` and `d.unl ≤ c.unl` (the opens bound only matters between a restart's
  `Open` and its `checkRestart`). So a purge to any `p ≤ d.unl` (what the purge law gives: the removed segment
  ends at or before the handle's `b ≤ d.unl`) stays within `c.pur` once `opOwnSnap` raises every candidate's
  `pur` to its `unl` (stored before the round), and `d.cut = segStart (first + 1) ≤ p`. Neither a tester bug nor a
  proof gap.

**Not done: items 2 and 5.**
- **Item 2, the purge law and the invariant's purge step** (with the crash's alternative layouts, session 4's
  choice). Everything on the handle's side is now in place: at `os.Remove(dir/nm)` with the remover's `osLock k i
  fd'`, `fileutil.lockKind k`, and `hj.cur !! nm = some (.file i)`, `nm` not the largest name: if `nm` is a lock's
  name, `fdLocks_excl` against its `walLockHI` refutes; otherwise `LkRel` gives its sequence below the first locked
  one, so (cuts increasing, `WalAbsD.cuts`) it ends at or before `b ≤ d.unl` (`walLks_agree`). Left: the law itself
  over `walOpenWF` (a sealed-handle update opening `walInv`, taking the claim's two halves for the name,
  `NameSplit.lean`), the layout step at the removal (`walAbsD_purge` with `p = d.unl`; `nm` is `lay.first`'s:
  the round removes oldest first), and the crash side: the removed-not-durable segments `pg` per directory and
  `CrashOkA`'s alternatives with a suffix of `pg` put back (session 4's design), which touches `CrashOkW`/`CrashTo`
  and every invariant step that rebuilds them.
- **Item 5, `purgeRound`**: not restored (Go untouched): it needs item 2, and specs for `fileutil.ReadDir` of the
  WAL directory under the handle's claim half and for `TryLockFile` relating the path to the inode `hj` maps it to.
  The spec shape stays session 4's (a caller-supplied repeatable commit, `□ ∀ d, Pc d -∗ …`).

**Next steps**: (1) the purge law (item 2's first part) as an update on `walOpenWF` — no invariant change; (2) the
`pg` crash bookkeeping; (3) `purgeRound`'s spec and proof, the Go restored, retranslated, `opOwnSnap` re-proved.

**Decisions left for the user**: none new (the trusted change's text, §4, still pending review). **No new axiom, no
`sorry`. No Go bug found.**

### Session 6 (2026-11-15, branch `wal-c-purge3`, base `origin/wal-int` `95c0f4e3f0`)

**Done** (each built with `lake build`; no new axiom, no `sorry`, nothing trusted changed, no Go changed, no
existing statement changed; all new files, so nothing else rebuilds):

- **The handle's side of the purge law** (`PurgeSafe.lean`): `walLockHI_excl`/`walLocksHI_excl` (a purger's
  `osLock k i fd'` of `fileutil`'s kind refutes any non-tail handle lock on `i`, `fdLocks_excl`, resources kept);
  `LkRel_purge` (pure: a `.wal` name, neither the tail's nor a locked one's, sequence `sq`, has `sq + 1 ≤ |cuts| -
  |ls|` and `segStart cuts (sq + 1) ≤ b`); `walDirLks_purge` (the two: `walDirLks` unfolded, `b` exposed with its
  `walTailsFrag`, so a caller holding the invariant gets `segStart cuts (sq + 1) ≤ b ≤ d.unl` by `walLks_agree`).
  `nm ≠ nm0` (not the tail) stays a premise: `purgeRound` has it from its count (`n + max < |fs|`, `max ≥ 1`, and
  `nm0` the largest `.wal` name, `walDirH`), or from the tail's `fdLocksW` the same way.
- **The remover's spec** (`Spec/os/RemoveN.lean`, `Proof/os/RemoveN.lean`, `Proof/os/UnlinkN.lean`):
  `os.Remove.specFileSncN`, `specFileSnc` with the name in a claim on any `N` (`N.Mem b`), outcome `rmFileOutN`;
  over the extension's unlink/unlink-none/rmdir-none specs generalized the same way (`wp_osUnlinkSN`,
  `wp_osUnlinkSN_none`, `wp_osRmdirSN_none`; the originals' proofs, kept in `LinuxFs/Proof/os/` so the extension
  does not rebuild). Why: the segment name is in the WAL directory's claim `(j, .except X, hj)`, half the handle's
  and half `walInv`'s; splitting `.only [nm]` out of it would leave the invariant's `WalDirClaim`/`DirKeysOk`
  broken for the duration of the call. With `specFileSncN` the purge's atomic update is `walCut_osAUnc`'s pattern
  (`CutAu.lean`): the handle's half with the caller, the invariant's half in the update, the claim replaced by its
  logged history at the commit (`replClaim`).
- **The crash side, pure** (`PurgeCrash.lean`, `PurgeRegion.lean`); the design below:
  `unpurge pg lay` (the removed-not-durable segments put back in front), `unpurge_purge` (a purge does not move
  it), `crashTo_unpurge` (`CrashTo` of `lay` gives it of the full layout), `crashTo_purgeD` (the purge's raise
  keeps `CrashTo`), `crashTo_cut_iff` (`CrashTo` does not read `cut`), `crashTo_dropFirst` (a crash keeping the
  `t`-th removal: from `CrashTo` of the tree with the name back, `CrashTo` of the tree without it), `walFullD`
  (the WAL with `cut` at the full layout's first segment), `WalAbsD.pur_mono`, `walAbsD_full_nil`,
  `walAbsD_full_purge` (the full layout's static relation survives a purge), `regionCrashedK_keptSet` (a crash
  keeping the removal keeps the claim's earlier entries and, with the name set back, is a crash of the claims
  before it).

**The crash design, settled** (supersedes session 4's "a list of alternative layouts"). A purge leaves the
*full* layout `F = unpurge pg lay` (the layout as of the last directory sync) unchanged, and `CrashTo F` already
quantifies over the kept suffix (`q`), so one layout covers every crash: none of the removals kept (`q ≤ |pg|`),
or all of them (the round's removes are sequential: a kept removal keeps the earlier ones, `regionCrashedK_keptSet`;
`crashTo_dropFirst`). A pending cut's alternative `alt` becomes `unpurge pg alt` (a cut's rename survives only with
every earlier removal, the same `Follows` argument). The invariant change:

1. `WalLay` gains `pg : List SegG := []` (the removed-not-durable segments of this WAL); `laysResF` holds their
   halves too (`segResP`: the crash's `FileCrashedR` needs them), `segsAll` lists them (inode `Nodup`).
2. `WalsOk`'s per-WAL clause keeps `WalAbsD d lay hj.cur` and replaces `CrashOkW d lay` by `(∃ ents0, WalAbsD
   (walFullD d lay.pg lay) (unpurge lay.pg lay) ents0) ∧ CrashOkW (walFullD d lay.pg lay) (unpurge lay.pg lay)`.
   With `pg = []` this is the old clause (`walAbsD_full_nil`, `unpurge_nil`, `walFullD d [] lay = d` given
   `WalAbsD.cut`).
3. Every step lemma that rebuilds the crash condition is applied to the full layout instead of `lay`: the crash
   step lemmas (`crashOkA_tail`, `crashOkW_tailW`, `crashOkA_win`, `crashOk_sync`, the resize steps, ...) use only
   `WalAbsD`'s `cuts`, `fit`, `intact`, `last`, `lastSynced`, `metas`, `synced` (checked by grep), which hold of
   the full layout; their `habs'` is built by the same builders applied to `F` (a tail step changes only the last
   segment, which `F` shares with `lay`). `crashGood_exists` (the crash) runs on `F` (`crashTo_cut_iff`).
4. The directory's fsync (`cut`'s `w.dirFile` sync, `crashOk_dirSync`'s site; `Create`'s) sets `pg := []`: every
   crash then keeps all removals, so `CrashTo F` with `q ≥ |pg|`, i.e. `CrashTo lay` (`crashTo_dropFirst` iterated),
   and the parked halves go back to the purger's caller or are dropped with the file.
5. **The purge step** (the commit of the purge's update, `walCut_osAUnc`'s shape): with the handle's tie
   (`walDirLks_purge`: `segStart lay.cuts (lay.first + 1) ≤ d.unl`, `nm` the first named segment since the round
   removes oldest first and only the handle's thread changes names): `Ls dir := { purgeLay lay with pg := lay.pg ++
   [g0] }`, `s.wal dir := walPurgeD d lay d.unl`, `WalAbsD` by `walAbsD_purge`, the full layout's by
   `walAbsD_full_purge`, the claim `replClaim … (hj.log x e c)`, the crash: dropped removal → old condition
   (`regionCrashedK_unlog`, `crashTo_purgeD`), kept → `regionCrashedK_keptSet` then `crashTo_dropFirst`.
   `d.cut` moves with it (the client's `walDiskAt`), so `purgeRound`'s spec takes the caller's repeatable commit
   (session 4's shape, `□ ∀ d, Pc d -∗ …`), which the tester supplies (session 5: its oracle covers it).

**Not done** (in order, each its own step):
1. The invariant change (items 1-4 above): the `WalLay.pg` field, `WalsOk`, `laysResF`/`segsAll`, the ~15 crash
   step sites (`etc/importers.py --uses CrashOkW`), `crashGood_exists`, the directory sync's drop. The largest
   piece; mechanical once (2) is decided.
2. The purge's update `walPurge_osAUnc` over `os.Remove.specFileSncN` (item 5), with the sealed-handle law
   lending the handle's claim half and path to `purgeRound` (`walOpenWF ⊢ … ∗ (… -∗ walOpenWF)`; the handle's
   relations survive the removal of an unlocked non-tail name: `LkRel` and `walDirH`'s facts only lose a name
   below the locked range).
3. `purgeRound` (item 2 of the brief): **not restored** (Go untouched): its call in `opOwnSnap` without a proof
   would put an unproved function under the tester's closed result. Needs (1)-(2) and specs already present
   (`fileutil.ReadDir`, which takes any claim fraction; `TryLockFile` through `fileutil.OpenTriple` instantiated
   with `os.OpenFile` on the claim half, giving the inode `hj.cur` maps the name to; `os.Remove.specFileSncN`).
4. Links: nothing new to link yet (no linked function changed; the new specs have no caller). `etc/gen-link.py
   --check` not rerun for that reason.

**Decisions left for the user**: none new. **No new axiom, no `sorry`. No Go bug found.**

### Session 7 (2026-11-15, branch `wal-c-purge4`, base `origin/wal-int` `16f1121760`)

**Done: item 1, the invariant change** (session 6's plan, with one deviation below). Built with `lake build`:
the WAL `Link`; the tester's and `durable`'s `Link`s: see the end of this entry. No new axiom, no `sorry`,
nothing trusted changed, no Go changed, no client-facing spec changed (so no ledger entry: no statement was
found false; the internal lemma statements below changed with the invariant).

- **The state.** `WalLay.pg : List SegG := []` (`Abs.lean`): the segments removed by purges, in front of
  `first`. `unpurge pg lay` and `walFullD d pg lay` moved to `Abs.lean` (`unpurge` now also sets `pg := []`,
  so the full layout has no removed segments of its own), with their projection `simp` lemmas,
  `unpurge_getLast?`, `walFullD_nil`, `walCrash_walFullD`, `WalAbsD.setPg`/`setCut`.
- **The invariant** (`Inv.lean`, `Cut.lean`):
  - `segsAll Ls` lists `lay.pg ++ lay.segs` of every layout (so `laysResF`, `walParked` and the inode
    `Nodup` cover the removed segments: their halves stay in the invariant, which a crash bringing them back
    needs, `FileCrashedR`); `laysRes` likewise.
  - `WalsOk`'s per-WAL clause: `WalAbsD d lay hj.cur ∧ WalFullOk d lay cl n`, where `WalFullOk` (new,
    `Cut.lean`) is `(∃ ents0, WalAbsD (walFullD d lay.pg lay) (unpurge lay.pg lay) ents0) ∧
    CrashOkW (walFullD d lay.pg lay) (unpurge lay.pg lay) cl n` (`walFullOk_nil`: with `pg = []` it is the
    old `CrashOkW d lay`).
  - `DirKeysOk`'s crash clause: `CrashOkA (walFullD d lay.pg lay) (unpurge lay.pg lay) none`.
  - `WalsNamed`'s crash clause: `SegsNamedC (lay.pg ++ lay.segs)` (a crash may bring a removed name back).
  - `WalsStart` (`CrashPure.lean`): its last clause also says `lay.pg = []`; `crashGood_exists` runs on the
    full layout and returns the crashed layout with `pg := []`.
- **Deviation from session 6, item 4: the directory's fsync does not drop `pg`.** Not needed for soundness
  (`CrashTo` of the full layout quantifies over the kept suffix, so it stays true once every removal is
  durable; `crashOk_dirSync` drops the cut's alternative on the full layouts as before), and dropping would
  need a new crash lemma (`CrashTo` of the full layout with the removed inodes absent gives `CrashTo` of
  `lay`) and the parked/invariant halves' release at `cut`'s sync, for no client benefit. So `pg` is the
  segments removed **this generation** (a crash resets it), and `unpurge lay.pg lay` the layout with all of
  them back; the names "as of the last directory sync" in `PurgeCrash.lean`'s header are now loose.
- **Machinery.** `PurgeFull.lean` (new, pure): `walAbsD_full_step` (the full layout's relation after any step
  that keeps `pg` and `first`, from the old full relation and the new layout's: segment starts, streams and
  history before `first` unchanged, `pur` not lowered, new names at or above old ones), `walAbsD_full_same`,
  `pg_le_first`; `crashTo_unpurge`, `crashTo_cut_iff` moved there from `PurgeCrash.lean`. Per step family:
  `walAbsD_full_tail` and `walFullOk_tail` (`TailStepPure.lean`), `tailLay_unpurge`, `syncLay_unpurge`,
  `syncLayW_unpurge`, `syncLayP_unpurge`, `cutLay_unpurge` (a step of the full layout is the full layout of
  the step), `TailCrashStepF` (`RzWals.lean`: the crash step of the full layout, which the resize/write
  steps' callers now prove by the same lemmas applied to the full relation), `crashOkA_cutF` (`CutLay.lean`:
  the cut's rename on the full layout: a crash keeping the rename keeps every earlier entry of the claim,
  so `CrashTo` of the new layout, `crashTo_synced`, then of the full one, `crashTo_unpurge`),
  `walInos_realize` (`CutCommitPure.lean`: entries listing given segments, for the full relation's `ents0`
  after a cut), `segsNamedC_pg`, `pg_walNameP` (`CutCommitLemmas.lean`), `repOld_unpurge`,
  `tailSynced_unpurge`, `walFullOk_mono`/`_named`/`_unl`, `laysResF_put` with `laysResF_del` restated (the
  rest keeps the layout with no named segments, `pg` in it), `segsAll_nodup_segs`/`_ne`, `sub_pg`,
  `mem_segsAll_all`/`_pg`, `segsAll_mem_nil`.
- **Internal statement changes** (no client spec): `walsOk_tail`, `dirKeysOk_tail` (+ `g.name = g0.name`);
  `walsOk_tailA`, `dirKeysOk_tailA` (the step a `TailCrashStepF`, + the name, + `WalsOk`); `walsOk_append`,
  `walsOk_sync`/`syncW`/`syncP`/`syncIdle` (their `CrashOk` premise on the full layout, which `DirKeysOk`
  gives); `walsOk_create`, `dirKeysOk_create`, `walsNamed_create`, `walParked_create`, `laysResF_insert`,
  `walCreate_osAUnc` (+ `lay.pg = []`; `Create`'s `createLay` has it by `rfl`); `walsNamed_relay`,
  `walParked_relay`, `segsAll_sep_relay` (+ `lay'.pg = lay.pg`); `syncLay_any`, `syncLay_anyP`, `syncLay_anyE`,
  the repair's (+ `L.pg = lay.pg` among the new layout's facts); `segsAll_mem`, `segsAll_nodup_iff`,
  `segsAll_nodup_sub`, `laysResF_map`, `segsAll_sep_map`, `CrashGood` (over `pg ++ segs`).
- A gotcha met: an `obtain` pattern `-` on a `WalsOk` clause's `hj` clears the `WalAbsD … hj.cur` after it
  too (it depends on `hj`); name `hj` when `habs` is needed.

**Not done: items 2 and 3.**
- **Item 2, the purge's update and step.** What it needs, now that the full layout is in place: (a) the pure
  step `walsOk_purge`/`dirKeysOk_purge`/`walsNamed_purge` (the layout `{ purgeLay lay with pg := lay.pg ++
  [g0] }`, `segsAll` unchanged as a list (`pg ++ g0 :: gs`), `WalAbsD` by `walAbsD_purge` with `p = d.unl`,
  the full relation by `walAbsD_full_purge` (its `pg` argument now `lay.pg`, `unpurge` resetting `pg`), the
  crash: the claim `replClaim … (hj.log x (rmFileEnt …) (delete nm hj.cur))`; a crash dropping the removal is
  one of the old claims (`regionCrashedK_unlog`), one keeping it is, with the name set back, one of the old
  claims keeping every earlier entry (`regionCrashedK_keptSet`), and `crashTo_dropFirst`; the old condition
  taken from `DirKeysOk`'s (no cut pending, so no alternative); the W1G/`FileCrashedR` premises at the crash
  with the name set back need the removed segment's (durable, intact) image: `w1G_durable`-style; then
  `walParked`'s claim replacement (`walParked_cut`'s claim part) and `walTailsRes` (the last segment kept:
  the purged one is not the tail); (b) the update `walPurge_osAUnc` over `os.Remove.specFileSncN`
  (`walCut_osAUnc`'s shape, the handle's claim half lent, `walDirLks_purge` for `segStart cuts (first + 1) ≤
  d.unl`, `nm` the first named segment); (c) the handle's side: `walOpenWF` lending the claim half and the
  path, `LkRel`/`walDirH` after the removal of an unlocked name below the locked range.
- **Item 3, `purgeRound`**: not restored (Go untouched), as session 6: it needs item 2.

**Decisions left for the user**: none new. **No new axiom, no `sorry`. No Go bug found.**
