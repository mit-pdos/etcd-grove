/-
Premises a client's theorem may state on its executions, beyond the Linux file extension's
semantics (`Impl.lean`) [Trusted definitions!]: the semantics restricted by a premise `SQ` on
steps and a premise `Q` on crashes (`fsSemWithS SQ Q`: step `FsStep ∧ SQ`, crash `OsCrash ∧ Q`). A
theorem proved over it holds of the executions that satisfy both: an assumption on the environment,
which the theorem states, and which none of the semantics' own rules make.

`SectorWhole` is a premise on crashes: a known limitation, assumed only for etcd's WAL
(`notes/STATUS.md`, "Known limitations"; `nonissues/etcd-wal-torn-tail-mid-sector.md`).
`NoIoErr` is a premise on steps: no I/O error on the files a set covers, an environment assumption
(approved by the user 2026-11-15, `notes/decisions.md`, "fsExt: no I/O errors on chosen files"; the
lock requests and directory reads added with the user's approval of 2026-11-19, option (a) of
`notes/wal-units/noioerr.md`, "Blocked"; the errnos of the `unlink`s and `rmdir`s that cannot succeed,
`PathErrno`, with the user's approval of 2026-11-19, item 3 narrowed, and of an `open` of an absent
name, with the user's approval of 2026-11-23, claim #34; the lock requests narrowed to the
blocking ones and the over-long paths left out, the user's decisions of 2026-11-19 after the attack on
F1's fix, `notes/wal-units/noioerr.md`, session 7; `flock` left to `NoMapLockErr`, which covers it
too, the user's decision of 2026-11-20).
-/
module

public import GooseLang.Ext.Fs.Impl

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

/-- A premise on the extension's steps: of the operation `op` on `v`, from `st` to `st'` with the
result `e'`. -/
abbrev StepPrem := ∀ [GooseExts] [GoGlobalContext], String → val → OsState → Expr → OsState → Prop

/-- The semantics whose steps are `FsStep`s satisfying `SQ` and whose crashes are `OsCrash`es
satisfying `Q`. -/
@[instance_reducible] def fsSemWithS (SQ : StepPrem) (Q : OsState → OsState → Prop) :
    ExtSemantics fsExt where
  step _ o v h st g e' h' st' g' := FsStep o v h st g e' h' st' g' ∧ SQ o v st e' st'
  crash st st' := OsCrash st st' ∧ Q st st'

/-- **SectorWhole** for the files at the paths `covers` holds, at a crash from `st` to `st'`: each
512-byte sector of such a file that holds a byte below its crash size comes back as one state of
that sector, as of some change `m` (each byte its candidate as of `m`, `valAt`): a crash never
mixes, within one sector, two changes, or a change's prefix with what was there before.

What it assumes, exactly: changes on a file never overlap in time (at most one is in flight, the
semantics' rule), so `valAt · m` is the page cache right after change `m` *when each change landed
all it announced*. A change that landed short (a short `pwrite`, or one that failed part way)
leaves the page cache in a state that is no stamp's, and this premise excludes a crash that keeps
such a state in a covered sector, as it excludes a sector torn by writeback.

A premise on executions, not a property of Linux: on configuration C one `pwrite` can reach disk
torn mid-sector (`notes/axiom-review/fs-v2-r6/e2e/`, mechanisms A and B). It is assumed only where
a client relies on it, etcd's WAL (`decoder.go`'s `isTornEntry` takes a torn tail to leave whole
sectors of zeros), as a known limitation (`notes/STATUS.md`, "Known limitations";
`nonissues/etcd-wal-torn-tail-mid-sector.md`; `examples/osfs/semantics/premise_sector_whole.go`).
For the WAL (one appender, each `pwrite` over preallocated zeros, a short write retried by Go's
loop) it says what `isTornEntry` needs: a torn tail sector is a sector of zeros or one write's.
Evidence: none that it holds; the WAL test on C (`notes/axiom-review/fs-v2-r6/wal/`) caught no
tail torn mid-sector on disk in 202 crash images, but the mechanisms that would tear one are
present in the WAL's code. A crash that keeps every covered byte as of its last sync satisfies it
(`m = 0`), so it never leaves a state without a crash. -/
def SectorWhole (covers : GoString → Prop) (st st' : OsState) : Prop :=
  ∀ p i f f', covers p → st.lookup p = some (.file i) → st.fs.files !! i = some f →
    st'.fs.files !! i = some f' → ∀ n, 512 * n < f'.size →
      ∃ m, ∀ j < 512, f'.cache (512 * n + j) = valAt (f.cand (512 * n + j)) m

/-! ## No I/O errors on chosen files -/

/-- The files a `NoIoErr` premise covers: by inode, at the state of the step (the calls on an fd or
on a change's token: `fsync`/`fdatasync`, `pwrite`'s end, `ftruncate`'s end, `fallocate`'s end,
`fstat`, `pread`, `close`, the OFD lock, and a directory fd's `fsync`, `close` and
read), and by path, the call's own argument (the calls on a path: `open`, `rename` (either path),
`mkdir`, `unlink`, `rmdir`). -/
structure IoSet where
  ino : OsState → Ino → Prop
  path : GoString → Prop

/-- **A path Linux accepts by its length**: shorter than `PATH_MAX` (4096 bytes, the terminating NUL
included: `getname` fails with `ENAMETOOLONG` at 4096), and no component longer than `NAME_MAX` (255
bytes: every run of 256 bytes holds a `/`; the walk fails with `ENAMETOOLONG` when it reaches a longer
component, `ext4_lookup`'s check, unless an earlier component is missing or not a directory, `ENOENT`/
`ENOTDIR` first). The semantics does not bound lengths (a longer path is given the outcomes of
a short one, a success included, which Linux never takes: more behaviours, sound); `NoIoErr` covers
only the paths that fit (2026-11-19, the user's decision on the attack's finding A1;
`examples/osfs/semantics/premise_no_io_err.go`, measured: `TestNoIoErrNameTooLong`). -/
def PathFits (p : GoString) : Prop :=
  p.length < 4096 ∧ ∀ q : GoString, q <:+: p → q.length = 256 → slashB ∈ q

section noIoErr
variable [GooseExts] [GoGlobalContext]

/-- The step of the operation `o` on `v` from `st` is a call on a file or a path that `S` covers. No
other operation is: not the first steps of a change (which make no system call and never fail), not
`mmap`/`munmap`, `fallocate(KEEP_SIZE)`, `lstat` (`LstatDir`: its outcome does not tell a failed
`lstat` of a directory from a non-directory, so there is no success to name), the model's queries
(`PathKind`, `FdKind`: one answer from each state, nothing to exclude), or the calls on a directory
outside the roots' trees. The OFD lock requests (`OfdLock`) and the directory reads (`DirReadNext`)
are covered on an fd of a covered inode (since 2026-11-19), a lock call only when it is blocking
(`fcntl(F_OFD_SETLKW)`): a non-blocking one may fail with `EAGAIN` whatever the model's locks
(`LockStep`, `locks_spurious_eagain.go`); a covered blocking one ends with errno 0 or waits (its wait, a
step since 2026-11-20, counts as `ErrnoZero`: the user's approval of option (A)). `flock` is not covered here: `NoMapLockErr` covers it (in the
same form, its non-blocking `EAGAIN` allowed; the user's decision of 2026-11-20: one premise per call, but for an `open` with no free fd, which both may name, `noIoErr_noMapLockErr_keeps`). A path call is covered only on
paths that fit (`PathFits`, each of `rename`'s two). -/
def IoCovers (S : IoSet) (o : String) (v : val) (st : OsState) : Prop :=
  match o with
  | "Fsync" | "Close" | "Fstat" =>
      ∃ (fd : w64) (d : OsFd), v = #fd ∧ FdOpen st fd d ∧ S.ino st d.ino
  | "PRead" => ∃ (fd : w64) (d : OsFd) (w : val), v = PairV (#fd) w ∧ FdOpen st fd d ∧ S.ino st d.ino
  | "PWriteFinish" | "FtruncateFinish" | "FallocFinish" =>
      ∃ (t : Nat) (c : OsChange), v = osTokV t ∧ st.proc.inflight !! t = some c ∧ S.ino st c.ino
  | "DirSync" | "DirClose" =>
      ∃ (fd : w64) (df : OsDirFd), v = #fd ∧ st.proc.dfds !! fd = some df ∧ S.ino st df.ino
  | "Open" => ∃ (t : Nat) (p : GoString) (fl : w64), v = PairV (osTokV t) (PairV (#p) (#fl)) ∧
      S.path p ∧ PathFits p
  | "Rename" => ∃ (k : Nat) (s t : GoString), v = PairV (osTokV k) (PairV (#s) (#t)) ∧
      (S.path s ∨ S.path t) ∧ PathFits s ∧ PathFits t
  | "Mkdir" | "Unlink" | "Rmdir" => ∃ (k : Nat) (p : GoString), v = PairV (osTokV k) (#p) ∧
      S.path p ∧ PathFits p
  | "OfdLock" => ∃ (fd cmd typ : w64) (d : OsFd), v = PairV (#fd) (PairV (#cmd) (#typ)) ∧
      FdOpen st fd d ∧ S.ino st d.ino ∧ cmd.toNat = F_OFD_SETLKW
  | "DirReadNext" => ∃ (fd : w64) (df : OsDirFd), v = #fd ∧ st.proc.dfds !! fd = some df ∧
      S.ino st df.ino
  | _ => False

/-- The outcome `e'` of the operation `o` has errno 0: a success. For a directory read
(`DirReadNext`), also `ENOENT`, which Linux answers for a removed directory, and only then
(`meta_enoent.go`): a read of a removed directory is not an I/O error. For a blocking OFD lock request
(`OfdLock`, covered only blocking), also the wait, the call stepping to itself (`LockStep`, 2026-11-20,
the user's approval of option (A)): so a covered blocking request ends with errno 0 or waits, never
fails (the semantics' only step to a call is the same call's wait). -/
def ErrnoZero (o : String) (e' : Expr) : Prop :=
  match o with
  | "PWriteFinish" | "Fstat" | "PRead" | "Open" => ∃ r : val, e' = osRes r 0
  | "OfdLock" => e' = Val (#(0 : w64)) ∨ ∃ w : val, e' = ExternalOp fsExt.name "OfdLock" (Val w)
  | "DirReadNext" => ∃ (b : GoString) (dn e : w64), e' = Val (PairV (#b) (PairV (#dn) (#e))) ∧
      (e = 0 ∨ e = ENOENT)
  | _ => e' = Val (#(0 : w64))

/-- `EISDIR`: Linux's errno for an `unlink(2)` of a directory (`may_delete`, `fs/namei.c`). -/
def EISDIR : w64 := 21

/-- `ENOTEMPTY`: ext4's errno for an `rmdir(2)` of a directory with an entry (`ext4_rmdir`,
`fs/ext4/namei.c`). -/
def ENOTEMPTY : w64 := 39

/-- **The errno Linux gives an `unlink`/`rmdir`/`open` that cannot succeed**, in the cases a client
needs (2026-11-19, the user's approval of item 3 of `notes/wal-units/noioerr.md`, narrowed; `open`
since 2026-11-23, the user's approval for claim #34, `wal.Exist`): of the call `o` on the path in
`v`, from `st`: `ENOENT` when the path has no entry and its parent is a directory (the last
component's lookup finds nothing: `unlink(2)`, `rmdir(2)`, and `open(2)` without `O_CREAT` from a
state with a free fd, the result fd `-1`); `EISDIR` for an `unlink` of a directory; `ENOTEMPTY` for an
`rmdir` of a directory with an entry. Nothing for any other case or call (an `open` with no free fd
included: Linux takes the fd first, `EMFILE`, and `NoMapLockErr` speaks of it). Each case is one
where the semantics has no success (`Impl.lean`: `Unlink` succeeds only on a file, `Rmdir` only on an
empty directory, both only where the entry exists; `Open` without `O_CREAT` only where the path
resolves, `OpenEffect`). -/
def PathErrno (o : String) (v : val) (st : OsState) (e' : Expr) : Prop :=
  match o with
  | "Unlink" => ∃ (k : Nat) (p : GoString), v = PairV (osTokV k) (#p) ∧
      ((st.lookup p = none ∧ st.ParentDir p) → e' = Val (#ENOENT)) ∧
      ((∃ j, st.lookup p = some (.dir j)) → e' = Val (#EISDIR))
  | "Rmdir" => ∃ (k : Nat) (p : GoString), v = PairV (osTokV k) (#p) ∧
      ((st.lookup p = none ∧ st.ParentDir p) → e' = Val (#ENOENT)) ∧
      ((∃ j b n, st.lookup p = some (.dir j) ∧ st.tree.entry j b = some n) →
        e' = Val (#ENOTEMPTY))
  | "Open" => ∃ (k : Nat) (p : GoString) (fl : w64), v = PairV (osTokV k) (PairV (#p) (#fl)) ∧
      ((fl.toNat / O_CREAT % 2 = 0 ∧ st.lookup p = none ∧ st.ParentDir p ∧ ∃ fd, FdFree st fd) →
        e' = osRes (#(-1 : w64)) ENOENT)
  | _ => True

end noIoErr

/-- **No I/O error on the files `S` covers**, a premise on steps: a step of a call on a file or path
`S` covers (`IoCovers`) has errno 0 whenever the semantics has an outcome with errno 0 for that call
from that state (`ErrnoZero`). It excludes, on those files: a failing `fsync`/`fdatasync` (`EIO`,
`ENOSPC`, `EDQUOT`); a `pwrite` ending with an errno (`EIO`, `ENOSPC`, `EDQUOT`, `EINTR`) where a write
of at least one byte could land (its offset below `maxBytes`, or no data); a failing `ftruncate` or
`fallocate` of a size up to `maxBytes`; a failing `fstat`, `pread` or `close` of a covered file, or
`fsync`/`close` of a covered directory; and a failing `open`, `rename`, `mkdir`, `unlink` or `rmdir`
on a covered path that fits (`PathFits`) where the call can succeed (the path resolves as the call
needs; the model always has a free fd for `open`, so `EMFILE`/`ENFILE` are excluded too, which the
environment's fd limits make true: `Impl.lean`'s "Environment", `env_config.go`). Since 2026-11-19 also: a failing blocking OFD lock request (`fcntl` with
`F_OFD_SETLKW`) on a covered file that no other description conflicts with (`LockConflict`: another
fd's, or one a live mapping holds after its fd's close, `MapDesc`; `ENOLCK`, `EINTR`, ...), and a
failing blocking OFD unlock (`F_OFD_SETLKW` with `F_UNLCK`) (`flock`: `NoMapLockErr`); since 2026-11-20
(the user's approval of option (A)), a failing blocking OFD lock request in conflict too: it waits
(its step to itself, `LockStep`, counts as `ErrnoZero`); a directory
read (`getdents64`, a step of `Readdirnames`) of a covered directory ending with an errno other than
`ENOENT` (`EIO`, `EINTR`, ...) while the directory has a name to return or is at its end.

What it does **not** exclude, because the semantics then has no success: `EFBIG` at `maxBytes`
(ext4's `s_maxbytes`), the failures of a path call that cannot succeed
in that state (`ENOENT`, `EEXIST`, `ENOTEMPTY`, `EISDIR`, ...); `ENOENT` from a read of
a directory (the semantics gives it only for a removed one); and nothing about a call `IoCovers`
does not name (`mmap`, `flock`, `lstat`, ...), a non-blocking OFD lock request (which may fail with `EAGAIN` while
another process holds a reference to a description the program closed, a `/proc/<pid>/fdinfo` read:
`locks_spurious_eagain.go`), or a path that does not fit (`ENAMETOOLONG`). But the errno of a failing `unlink`/`rmdir` of a covered path
that cannot succeed is Linux's (since 2026-11-19, `PathErrno`, asked only where the semantics has no outcome with errno 0): `ENOENT` for an absent entry in an
existing directory, `EISDIR` for an `unlink` of a directory, `ENOTEMPTY` for an `rmdir` of a
non-empty directory (no I/O error, no lack of memory, no signal changes it into another); and so is
that of a failing `open` without `O_CREAT` of a covered path with no entry whose parent is a
directory, from a state with a free fd: `ENOENT` (approved by the user 2026-11-23, claim #34: Go's
`wal.Exist` answers false only on `os.ErrNotExist`, and true on any other error of its `ReadDir`;
measured as support: `TestNoIoErrOpenAbsent`).

An environment assumption, not a property of Linux (evidence: assumed): the device returns no I/O
error, the filesystem has room for these files, the kernel has memory for their locks and reads, and
no signal interrupts these calls; and no other process locks or unlocks them, through any description
(its own open, or a copy of the program's: `pidfd_getfd`, `SCM_RIGHTS`) (as the semantics' lock rule
already takes the roots' files to be the process's own, `examples/osfs/semantics/locks_ofd.go`)
(`examples/osfs/semantics/premise_no_io_err.go`). **Permissions** (configuration C's environment,
`Impl.lean`'s "Environment"; 2026-11-19, the user's approvals via etcd-grove-03): the process may search
every ancestor of a root and search and write every covered directory, and read and write every covered
file (no `EACCES`, on the walk or on an `open` for writing), no covered directory's sticky bit denies a
removal or rename, no covered file or directory has the immutable or append-only attribute, the sysctls
`fs.protected_symlinks` and `fs.protected_regular` deny nothing, an idmapped mount (if any) maps the
process's fsuid and fsgid (no `EOVERFLOW` from `may_create`), and no Linux security module, seccomp
filter or fanotify permission event denies or fails a call on them (no `EPERM`/`EACCES` from
`may_delete`, `may_create`, `inode_permission` or an LSM hook; no `SECCOMP_RET_ERRNO`; no `FAN_DENY`);
measured as contrasts in `premise_no_io_err_test.go` (`TestNoIoErrPermissions`, `TestNoIoErrPermAncestor`,
`TestNoIoErrPermFileWrite`, `TestNoIoErrProtectedSymlinks`, `TestNoIoErrProtectedRegular`).
**Fds and locks** (configuration C's environment too; 2026-11-19, the user's decisions on the attack's
findings F2' and F1'): at every `open` the process holds fewer fds than its `RLIMIT_NOFILE` soft limit
and the system's open files are below `fs.file-max` (no `EMFILE`/`ENFILE`; measured as a contrast:
`TestNoIoErrEmfile`); and no fd is closed while a lock call on it is in flight
(`env_no_close_during_lock.go`).
It is the condition under which etcd's server is shown not to panic where it calls `lg.Panic` on a
WAL error (`Create`, `SaveSnapshot`, `ReleaseLockTo`, `Close`, ...): approved by the user
2026-11-15 (`notes/decisions.md`, "fsExt: no I/O errors on chosen files"). It never leaves a state
without a step: whenever the semantics has a step, it has one the premise allows (`noIoErr_keeps`,
`GooseLang/Ext/Fs/NoIoErr.lean`). -/
def NoIoErr (S : IoSet) : StepPrem := fun o v st e' _ =>
  IoCovers S o v st →
    let succ := ∃ e'' st'', IsFsStep o v st e'' st'' ∧ ErrnoZero o e''
    (succ → ErrnoZero o e') ∧ (¬ succ → PathErrno o v st e')

/-! ## No errors of `flock`, `mmap`, `munmap` on chosen files, and `open` with no free fd (pending the user's review) -/

/-- `ENOMEM`: what a failing `mmap(2)` returns when the process has no room in its address space
for the mapping, or is at its map count or `RLIMIT_AS` (an error `NoMapLockErr` excludes; with no
room, the model's `mmap` may not return instead, `MmapStall`). -/
def ENOMEM : w64 := 12

section noMapLockErr
variable [GooseExts] [GoGlobalContext]

/-- The step of the operation `o` on `v` from `st` is a lock or mapping call on a file `S` covers, by
inode at the step: `flock` and `mmap` on an fd of the file, `munmap` and `madvise` (2026-11-17,
pending the user's review) of a mapping of it, by its base; or an `open`
of a path `S` covers (by path, its argument) from a state with **no free fd** (`FdFree`: every
nonnegative fd taken; 2026-11-17, pending the user's review). -/
def MapLockCovers (S : IoSet) (o : String) (v : val) (st : OsState) : Prop :=
  match o with
  | "Flock" => ∃ (fd how : w64) (d : OsFd), v = PairV (#fd) (#how) ∧ FdOpen st fd d ∧ S.ino st d.ino
  | "Mmap" => ∃ (fd : w64) (w : val) (d : OsFd), v = PairV (#fd) w ∧ FdOpen st fd d ∧ S.ino st d.ino
  | "Munmap" => ∃ (base : Loc) (w : val) (m : OsMap), v = PairV (#base) w ∧
      st.proc.maps !! base = some m ∧ S.ino st m.ino
  | "Open" => (∃ (t : Nat) (p : GoString) (fl : w64), v = PairV (osTokV t) (PairV (#p) (#fl)) ∧
      S.path p) ∧ ∀ fd, ¬ FdFree st fd
  | "Madvise" => ∃ (base : Loc) (w : val) (m : OsMap), v = PairV (#base) w ∧
      st.proc.maps !! base = some m ∧ S.ino st m.ino
  | _ => False

/-- The outcome `e'` of the operation `o` on `v` is no error of the environment: errno 0; for a
non-blocking `flock` lock request (`LOCK_SH` or `LOCK_EX` with `LOCK_NB`), also `EAGAIN`, the
conflict with another description's lock (no error: the caller's to handle, bbolt's `flock` retries
on it); for a blocking `flock` lock request, also its wait, the call stepping to itself (`LockStep`,
2026-11-20, the user's approval of option (A): a covered blocking request ends with errno 0 or waits);
for `mmap`, also the step to itself with no room in the address space (`MmapStall`: the
call does not return, Go's out of memory; see `NoMapLockErr`); for `open` with no free fd,
`EINTR` with the fd `-1`, which every model of `open` in `TrustedCode/os.lean` retries, so the Go
call does not return (out of descriptors, as out of memory; see `NoMapLockErr`), or errno 0 (a
success, which the semantics does not have with no free fd). -/
def MapLockOk (o : String) (v : val) (e' : Expr) : Prop :=
  match o with
  | "Open" => (∃ r : val, e' = osRes r 0) ∨ e' = osRes (#(-1 : w64)) EINTR
  | "Flock" => e' = Val (#(0 : w64)) ∨
      (∃ (fd how : w64) (ex : Bool), v = PairV (#fd) (#how) ∧ flockReq how.toNat = some (some ex, true) ∧
        e' = Val (#EAGAIN)) ∨
      e' = ExternalOp fsExt.name "Flock" (Val v)
  | "Mmap" => (∃ r : val, e' = osRes r 0) ∨ e' = ExternalOp fsExt.name "Mmap" (Val v)
  | _ => e' = Val (#(0 : w64))

end noMapLockErr

/-- **No error of `flock`, `mmap` or `munmap` on the files `S` covers** (pending the user's review),
a premise on steps beside `NoIoErr`: a step of one of these calls on a file `S` covers
(`MapLockCovers`) has an outcome `MapLockOk` whenever the semantics has such an outcome for that call
from that state. It excludes, on those files: a failing `flock` lock request where it can succeed
(no conflicting lock: `ENOLCK`, `EINTR`, ...), a non-blocking one failing with another errno than
`EWOULDBLOCK` on a conflict, a failing `LOCK_UN` (which can always succeed); every failing `mmap`
(`ENOMEM`, `EAGAIN`, `ENFILE`, `ENODEV`, `EOVERFLOW`, `EPERM`, ...: the semantics' success is there
whenever the arguments are accepted, so a covered `mmap` returns a mapping, or, with no room left
for it in `(0, maxAddr]`, does not return, `MmapStall`); a failing `munmap` of a whole mapping
(which can always succeed), whether or not it unmapped; a failing `madvise` with a paging hint of
a mapping of the file (`EAGAIN`, `ENOMEM`, ...: the semantics' success is always there; 2026-11-17,
pending the user's review).

**Out of descriptors** (2026-11-17, pending the user's review): a covered `open` from a state with no
free fd (all `2 ^ 63` nonnegative fds of the model taken) fails with `EINTR`, nothing created or
truncated but what the semantics' failure allows, never with `EMFILE` or another errno; every model of
`open` (`os.OpenFile`, `os.Stat`'s, the directory opens, `TrustedCode/os.lean`) retries `EINTR`, so the
Go call does not return there: fd exhaustion is treated as memory exhaustion (`mmap` above, Perennial's
`AllocOOMS`), outside the model. The semantics' `open` has no success with no free fd, so `NoIoErr`
(which asks errno 0 only where a success exists) keeps every errno there; this clause is what makes a
covered `open` that resolves its path never fail. Linux's own limit is far below the model's
(`EMFILE` at `RLIMIT_NOFILE`, `examples/osfs/semantics/premise_no_map_lock_err.go`), and `NoIoErr`
already excludes `EMFILE` on a covered path wherever the model has a free fd; the model's state with
none takes `2 ^ 63` opens, more than a run's steps (`receiptBound`). With a free fd this clause says
nothing (the two premises name disjoint steps, `noIoErr_noMapLockErr_keeps`).

What it does **not** exclude: a blocking `flock` request's wait on a conflict (the semantics has no
success there, `LockStep`; since 2026-11-20, the user's approval of option (A), the wait is a step and
the failures there are excluded: such a request waits, as on Linux, `locks_blocking.go`); `mmap`'s step to itself when the address space has no room (the process's
address space is shared by the mappings and the Go heap, both in `(0, maxAddr]`, and a premise on
steps does not see the heap: the stall, a step of the semantics that sees it, is what is left from a
state whose heap leaves no room, so the premise keeps a step there, `StepKeeps`; the model treats
running out of address space as the Go runtime's out of memory, outside the model, as Perennial's
`AllocOOMS`). Nor anything about the OFD lock (`fcntl`): `NoIoErr` covers its blocking requests.

An environment assumption, not a property of Linux (evidence: assumed): the kernel's lock and
mapping calls do not fail on these files for want of kernel memory or descriptors, no signal interrupts
their blocking `flock` requests (the Go runtime installs every handler with `SA_RESTART`, measured:
`locks_blocking.go`), no other process locks them (as `NoIoErr`'s assumption), the process is
below its map count (`vm.max_map_count`) and its `RLIMIT_AS`, and no seal, `noexec` mount or
file-system type refuses a shared read-only mapping
(`examples/osfs/semantics/premise_no_map_lock_err.go`). It is the condition (with `NoIoErr`) under
which bbolt's `Close` is shown to return no error (`Spec/go_etcd_io/bbolt/DB__Close_noErr.lean`),
where etcd's backend panics on its error (`applySnapshot`), and the one `Open` (its `flock` and
`mmap`) needs too (`NoMapLockErrSpecs.lean`). It never leaves a state without a step
(`noMapLockErr_keeps`, `GooseLang/Ext/Fs/NoMapLockErr.lean`). -/
def NoMapLockErr (S : IoSet) : StepPrem := fun o v st e' _ =>
  MapLockCovers S o v st → (∃ e'' st'', IsFsStep o v st e'' st'' ∧ MapLockOk o v e'') →
    MapLockOk o v e'

end Fs
end Perennial

end
