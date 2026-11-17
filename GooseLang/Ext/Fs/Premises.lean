/-
Premises a client's theorem may state on its executions, beyond the Linux file extension's
semantics (`Impl.lean`) [Trusted definitions!]: the semantics restricted by a premise `SQ` on
steps and a premise `Q` on crashes (`fsSemWithS SQ Q`: step `FsStep ∧ SQ`, crash `OsCrash ∧ Q`). A
theorem proved over it holds of the executions that satisfy both: an assumption on the environment,
which the theorem states, and which none of the semantics' own rules make.

`SectorWhole` is a premise on crashes: a known limitation, assumed only for etcd's WAL
(`notes/STATUS.md`, "Known limitations"; `nonissues/etcd-wal-torn-tail-mid-sector.md`).
`NoIoErr` is a premise on steps: no I/O error on the files a set covers, an environment assumption
(approved by the user 2026-11-15, `notes/decisions.md`, "fsExt: no I/O errors on chosen files").
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
`fstat`, `pread`, `close`, and a directory fd's `fsync` and `close`), and by path, the call's own
argument (the calls on a path: `open`, `rename` (either path), `mkdir`, `unlink`, `rmdir`). -/
structure IoSet where
  ino : OsState → Ino → Prop
  path : GoString → Prop

section noIoErr
variable [GooseExts] [GoGlobalContext]

/-- The step of the operation `o` on `v` from `st` is a call on a file or a path that `S` covers. No
other operation is: not the first steps of a change (which make no system call and never fail), not
`flock` or the OFD lock (the lock calls), not `mmap`/`munmap`, `fallocate(KEEP_SIZE)`, `lstat`, the
directory reads, or the calls on a directory outside the roots' trees. -/
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
  | _ => False

/-- The outcome `e'` of the operation `o` has errno 0: a success. -/
def ErrnoZero (o : String) (e' : Expr) : Prop :=
  match o with
  | "PWriteFinish" | "Fstat" | "PRead" | "Open" => ∃ r : val, e' = osRes r 0
  | _ => e' = Val (#(0 : w64))

end noIoErr

/-- **No I/O error on the files `S` covers**, a premise on steps: a step of a call on a file or path
`S` covers (`IoCovers`) has errno 0 whenever the semantics has an outcome with errno 0 for that call
from that state (`ErrnoZero`). It excludes, on those files: a failing `fsync`/`fdatasync` (`EIO`,
`ENOSPC`, `EDQUOT`); a `pwrite` ending with an errno (`EIO`, `ENOSPC`, `EDQUOT`, `EINTR`) where a write
of at least one byte could land (its offset below `maxBytes`, or no data); a failing `ftruncate` or
`fallocate` of a size up to `maxBytes`; a failing `fstat`, `pread` or `close` of a covered file, or
`fsync`/`close` of a covered directory; and a failing `open`, `rename`, `mkdir`, `unlink` or `rmdir`
on a covered path where the call can succeed (the path resolves as the call needs, a free fd for
`open`).

What it does **not** exclude, because the semantics then has no success: `EFBIG` at `maxBytes`
(ext4's `s_maxbytes`), `EMFILE` with no free fd, and the failures of a path call that cannot succeed
in that state (`ENOENT`, `EEXIST`, `ENOTEMPTY`, `EISDIR`, ...); and nothing about a call `IoCovers`
does not name (`flock` and the OFD lock among them, `mmap`, the directory reads).

An environment assumption, not a property of Linux (evidence: assumed): the device returns no I/O
error and the filesystem has room for these files (`examples/osfs/semantics/premise_no_io_err.go`).
It is the condition under which etcd's server is shown not to panic where it calls `lg.Panic` on a
WAL error (`Create`, `SaveSnapshot`, `ReleaseLockTo`, `Close`, ...): approved by the user
2026-11-15 (`notes/decisions.md`, "fsExt: no I/O errors on chosen files"). It never leaves a state
without a step: whenever the semantics has a step, it has one the premise allows (`noIoErr_keeps`,
`GooseLang/Ext/Fs/NoIoErr.lean`). -/
def NoIoErr (S : IoSet) : StepPrem := fun o v st e' _ =>
  IoCovers S o v st → (∃ e'' st'', IsFsStep o v st e'' st'' ∧ ErrnoZero o e'') → ErrnoZero o e'

/-! ## No errors of `flock`, `mmap`, `munmap` on chosen files (pending the user's review) -/

/-- `ENOMEM`: what a failing `mmap(2)` returns when the process has no room in its address space
for the mapping (`NoMapLockErr` keeps it). -/
def ENOMEM : w64 := 12

section noMapLockErr
variable [GooseExts] [GoGlobalContext]

/-- The step of the operation `o` on `v` from `st` is a lock or mapping call on a file `S` covers, by
inode at the step: `flock` and `mmap` on an fd of the file, `munmap` of a mapping of it. -/
def MapLockCovers (S : IoSet) (o : String) (v : val) (st : OsState) : Prop :=
  match o with
  | "Flock" => ∃ (fd how : w64) (d : OsFd), v = PairV (#fd) (#how) ∧ FdOpen st fd d ∧ S.ino st d.ino
  | "Mmap" => ∃ (fd : w64) (w : val) (d : OsFd), v = PairV (#fd) w ∧ FdOpen st fd d ∧ S.ino st d.ino
  | "Munmap" => ∃ (base : Loc) (w : val) (m : OsMap), v = PairV (#base) w ∧
      st.proc.maps !! base = some m ∧ S.ino st m.ino
  | _ => False

/-- The outcome `e'` of the operation `o` on `v` is no error of the environment: errno 0; for a
non-blocking `flock` lock request (`LOCK_SH` or `LOCK_EX` with `LOCK_NB`), also `EAGAIN`, the conflict with another description's lock (no
error: the caller's to handle, bbolt's `flock` retries on it); for `mmap`, also `ENOMEM`, no room in
the address space (see `NoMapLockErr`). -/
def MapLockOk (o : String) (v : val) (e' : Expr) : Prop :=
  match o with
  | "Flock" => e' = Val (#(0 : w64)) ∨
      ∃ (fd how : w64) (ex : Bool), v = PairV (#fd) (#how) ∧ flockReq how.toNat = some (some ex, true) ∧
        e' = Val (#EAGAIN)
  | "Mmap" => (∃ r : val, e' = osRes r 0) ∨ e' = osRes (#null) ENOMEM
  | _ => e' = Val (#(0 : w64))

end noMapLockErr

/-- **No error of `flock`, `mmap` or `munmap` on the files `S` covers** (pending the user's review),
a premise on steps beside `NoIoErr`: a step of one of these calls on a file `S` covers
(`MapLockCovers`) has an outcome `MapLockOk` whenever the semantics has such an outcome for that call
from that state. It excludes, on those files: a failing `flock` lock request where it can succeed
(no conflicting lock: `ENOLCK`, `EINTR`, ...), a non-blocking one failing with another errno than
`EWOULDBLOCK` on a conflict, a failing `LOCK_UN` (which can always succeed); a failing `mmap` with
another errno than `ENOMEM` (`EAGAIN`, `ENFILE`, `ENODEV`, `EOVERFLOW`, `EPERM`, ...); a failing
`munmap` of a whole mapping (which can always succeed), whether or not it unmapped.

What it does **not** exclude: a blocking `flock` request on a conflict (the semantics has no success
there, `LockStep`); `mmap`'s `ENOMEM`. The process's address space is shared by the mappings and
the Go heap (both in `(0, maxAddr]`), and a premise on steps sees the extension's state, not the
heap, so it cannot tell when the address space has room; excluding `ENOMEM` would leave no step
from a state whose heap leaves no room, which no premise may do (`StepKeeps`). (Go's own allocator
does not return there: an allocation with no room loops, Perennial's `AllocOOMS`.) Nor anything
about the OFD lock (`fcntl`), which `NoIoErr` does not name either.

An environment assumption, not a property of Linux (evidence: assumed): the kernel's lock and
mapping calls do not fail on these files for want of kernel memory or descriptors, and no seal,
`noexec` mount or file-system type refuses a shared read-only mapping
(`examples/osfs/semantics/premise_no_map_lock_err.go`). It is the condition (with `NoIoErr`) under which
bbolt's `Close` is shown to return no error (`Spec/go_etcd_io/bbolt/DB__Close_noErr.lean`), where
etcd's backend panics on its error (`applySnapshot`), and the one `Open` (its `flock` and `mmap`)
needs too, but for `mmap`'s `ENOMEM`. It never
leaves a state without a step (`noMapLockErr_keeps`, `GooseLang/Ext/Fs/NoMapLockErr.lean`). -/
def NoMapLockErr (S : IoSet) : StepPrem := fun o v st e' _ =>
  MapLockCovers S o v st → (∃ e'' st'', IsFsStep o v st e'' st'' ∧ MapLockOk o v e'') →
    MapLockOk o v e'

end Fs
end Perennial

end
