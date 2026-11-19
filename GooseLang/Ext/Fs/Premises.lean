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
`PathErrno`, with the user's approval of 2026-11-19, item 3 narrowed).
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
  step o v h st g e' h' st' g' := FsStep o v h st g e' h' st' g' ∧ SQ o v st e' st'
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
`fstat`, `pread`, `close`, `flock` and the OFD lock, and a directory fd's `fsync`, `close` and
read), and by path, the call's own argument (the calls on a path: `open`, `rename` (either path),
`mkdir`, `unlink`, `rmdir`). -/
structure IoSet where
  ino : OsState → Ino → Prop
  path : GoString → Prop

section noIoErr
variable [GooseExts] [GoGlobalContext]

/-- The step of the operation `o` on `v` from `st` is a call on a file or a path that `S` covers. No
other operation is: not the first steps of a change (which make no system call and never fail), not
`mmap`/`munmap`, `fallocate(KEEP_SIZE)`, `lstat` (`LstatDir`: its outcome does not tell a failed
`lstat` of a directory from a non-directory, so there is no success to name), the model's queries
(`PathKind`, `FdKind`: one answer from each state, nothing to exclude), or the calls on a directory
outside the roots' trees. The lock requests (`Flock`, `OfdLock`) and the directory reads
(`DirReadNext`) are covered on an fd of a covered inode (since 2026-11-19). -/
def IoCovers (S : IoSet) (o : String) (v : val) (st : OsState) : Prop :=
  match o with
  | "Fsync" | "Close" | "Fstat" =>
      ∃ (fd : w64) (d : OsFd), v = #fd ∧ FdOpen st fd d ∧ S.ino st d.ino
  | "PRead" => ∃ (fd : w64) (d : OsFd) (w : val), v = PairV (#fd) w ∧ FdOpen st fd d ∧ S.ino st d.ino
  | "PWriteFinish" | "FtruncateFinish" | "FallocFinish" =>
      ∃ (t : Nat) (c : OsChange), v = osTokV t ∧ st.proc.inflight !! t = some c ∧ S.ino st c.ino
  | "DirSync" | "DirClose" =>
      ∃ (fd : w64) (df : OsDirFd), v = #fd ∧ st.proc.dfds !! fd = some df ∧ S.ino st df.ino
  | "Open" => ∃ (t : Nat) (p : GoString) (fl : w64), v = PairV (osTokV t) (PairV (#p) (#fl)) ∧ S.path p
  | "Rename" => ∃ (k : Nat) (s t : GoString), v = PairV (osTokV k) (PairV (#s) (#t)) ∧
      (S.path s ∨ S.path t)
  | "Mkdir" | "Unlink" | "Rmdir" => ∃ (k : Nat) (p : GoString), v = PairV (osTokV k) (#p) ∧ S.path p
  | "Flock" => ∃ (fd how : w64) (d : OsFd), v = PairV (#fd) (#how) ∧ FdOpen st fd d ∧ S.ino st d.ino
  | "OfdLock" => ∃ (fd cmd typ : w64) (d : OsFd), v = PairV (#fd) (PairV (#cmd) (#typ)) ∧
      FdOpen st fd d ∧ S.ino st d.ino
  | "DirReadNext" => ∃ (fd : w64) (df : OsDirFd), v = #fd ∧ st.proc.dfds !! fd = some df ∧
      S.ino st df.ino
  | _ => False

/-- The outcome `e'` of the operation `o` has errno 0: a success. For a directory read
(`DirReadNext`), also `ENOENT`, which Linux answers for a removed directory, and only then
(`meta_enoent.go`): a read of a removed directory is not an I/O error. -/
def ErrnoZero (o : String) (e' : Expr) : Prop :=
  match o with
  | "PWriteFinish" | "Fstat" | "PRead" | "Open" => ∃ r : val, e' = osRes r 0
  | "DirReadNext" => ∃ (b : GoString) (dn e : w64), e' = Val (PairV (#b) (PairV (#dn) (#e))) ∧
      (e = 0 ∨ e = ENOENT)
  | _ => e' = Val (#(0 : w64))

/-- `EISDIR`: Linux's errno for an `unlink(2)` of a directory (`may_delete`, `fs/namei.c`). -/
def EISDIR : w64 := 21

/-- `ENOTEMPTY`: ext4's errno for an `rmdir(2)` of a directory with an entry (`ext4_rmdir`,
`fs/ext4/namei.c`). -/
def ENOTEMPTY : w64 := 39

/-- **The errno Linux gives an `unlink`/`rmdir` that cannot succeed**, in the cases a client needs
(2026-11-19, the user's approval of item 3 of `notes/wal-units/noioerr.md`, narrowed): of the call
`o` on the path in `v`, from `st`: `ENOENT` when the path has no entry and its parent is a directory
(the last component's lookup finds nothing: `unlink(2)`, `rmdir(2)`); `EISDIR` for an `unlink` of a
directory; `ENOTEMPTY` for an `rmdir` of a directory with an entry. Nothing for any other case or
call. Each case is one where the semantics has no success (`Impl.lean`: `Unlink` succeeds only on a
file, `Rmdir` only on an empty directory, both only where the entry exists). -/
def PathErrno (o : String) (v : val) (st : OsState) (e' : Expr) : Prop :=
  match o with
  | "Unlink" => ∃ (k : Nat) (p : GoString), v = PairV (osTokV k) (#p) ∧
      ((st.lookup p = none ∧ st.ParentDir p) → e' = Val (#ENOENT)) ∧
      ((∃ j, st.lookup p = some (.dir j)) → e' = Val (#EISDIR))
  | "Rmdir" => ∃ (k : Nat) (p : GoString), v = PairV (osTokV k) (#p) ∧
      ((st.lookup p = none ∧ st.ParentDir p) → e' = Val (#ENOENT)) ∧
      ((∃ j b n, st.lookup p = some (.dir j) ∧ st.tree.entry j b = some n) →
        e' = Val (#ENOTEMPTY))
  | _ => True

end noIoErr

/-- **No I/O error on the files `S` covers**, a premise on steps: a step of a call on a file or path
`S` covers (`IoCovers`) has errno 0 whenever the semantics has an outcome with errno 0 for that call
from that state (`ErrnoZero`). It excludes, on those files: a failing `fsync`/`fdatasync` (`EIO`,
`ENOSPC`, `EDQUOT`); a `pwrite` ending with an errno (`EIO`, `ENOSPC`, `EDQUOT`, `EINTR`) where a write
of at least one byte could land (its offset below `maxBytes`, or no data); a failing `ftruncate` or
`fallocate` of a size up to `maxBytes`; a failing `fstat`, `pread` or `close` of a covered file, or
`fsync`/`close` of a covered directory; and a failing `open`, `rename`, `mkdir`, `unlink` or `rmdir`
on a covered path where the call can succeed (the path resolves as the call needs, a free fd for
`open`). Since 2026-11-19 also: a failing lock request (`flock`, or `fcntl` with `F_OFD_SETLK`/
`F_OFD_SETLKW`) on a covered file that no other description conflicts with (`LockConflict`: another
fd's, or one a live mapping holds after its fd's close, `MapDesc`; `ENOLCK`, `EINTR`, ...), and a failing unlock; a directory read (`getdents64`, a step of
`Readdirnames`) of a covered directory ending with an errno other than `ENOENT` (`EIO`, `EINTR`, ...)
while the directory has a name to return or is at its end.

What it does **not** exclude, because the semantics then has no success: `EFBIG` at `maxBytes`
(ext4's `s_maxbytes`), `EMFILE` with no free fd, the failures of a path call that cannot succeed
in that state (`ENOENT`, `EEXIST`, `ENOTEMPTY`, `EISDIR`, ...), and the failure of a lock request
that conflicts with a lock another description holds (another fd's, or one a live mapping keeps
after its fd's close: `EAGAIN`, ...); `ENOENT` from a read of
a directory (the semantics gives it only for a removed one); and nothing about a call `IoCovers`
does not name (`mmap`, `lstat`, ...). But the errno of a failing `unlink`/`rmdir` of a covered path
that cannot succeed is Linux's (since 2026-11-19, `PathErrno`, asked only where the semantics has no outcome with errno 0): `ENOENT` for an absent entry in an
existing directory, `EISDIR` for an `unlink` of a directory, `ENOTEMPTY` for an `rmdir` of a
non-empty directory (no I/O error, no lack of memory, no signal changes it into another).

An environment assumption, not a property of Linux (evidence: assumed): the device returns no I/O
error, the filesystem has room for these files, the kernel has memory for their locks and reads, and
no signal interrupts these calls; and no other process locks them (as the semantics' lock rule
already takes the roots' files to be the process's own, `examples/osfs/semantics/locks_ofd.go`)
(`examples/osfs/semantics/premise_no_io_err.go`). **Permissions** (configuration C's environment,
`Impl.lean`'s "Environment"; 2026-11-19, the user's approval via etcd-grove-03): the process may search
and write every covered directory (no `EACCES`), no covered directory's sticky bit denies a removal or
rename, no covered file or directory has the immutable or append-only attribute, and no Linux security
module denies a path call on them (no `EPERM`/`EACCES` from `may_delete`, `may_create`, `inode_permission`
or an LSM hook); measured as a contrast in `premise_no_io_err_test.go`'s `TestNoIoErrPermissions`.
It is the condition under which etcd's server is shown not to panic where it calls `lg.Panic` on a
WAL error (`Create`, `SaveSnapshot`, `ReleaseLockTo`, `Close`, ...): approved by the user
2026-11-15 (`notes/decisions.md`, "fsExt: no I/O errors on chosen files"). It never leaves a state
without a step: whenever the semantics has a step, it has one the premise allows (`noIoErr_keeps`,
`GooseLang/Ext/Fs/NoIoErr.lean`). -/
def NoIoErr (S : IoSet) : StepPrem := fun o v st e' _ =>
  IoCovers S o v st →
    let succ := ∃ e'' st'', IsFsStep o v st e'' st'' ∧ ErrnoZero o e''
    (succ → ErrnoZero o e') ∧ (¬ succ → PathErrno o v st e')

end Fs
end Perennial

end
