/-
The Linux file extension of GooseLang [Trusted definitions!].

A node's regular files as Linux exposes them to one process through `pread`, `pwrite`,
`fstat`, `ftruncate`, `fdatasync`/`fsync`, `close` and a read-only shared `mmap`: the page
cache that reads and the mappings see, the image on disk that a crash keeps, and the fds and
mappings of the process. It is named after `os` (`osFsExt.name`); this repository translates
`os`, `syscall` and `golang.org/x/sys/unix` itself (project `bboltfs` of `etc/goose.py`), and
their trusted models (`TrustedCode/os.lean`, `syscall.lean`, `golang_org/x/sys/unix.lean`) call
the operations below and marshal Go values. The design and its
decisions (D1–D8) are in `notes/osfs-ext-plan.md`.

**Environment** (hypotheses of the adequacy statement, not of this file): the paths in the
domain of `files` name distinct regular files on a local ext4 or xfs filesystem; no other
process touches them; the device honours cache flushes, writes each sector atomically and has no
media errors (a torn sector would garble durable neighbours of a dirty byte, and a read error on
a mapped page is SIGBUS where the model's load succeeds). Opening any other path is stuck, so
path resolution is never modelled.

**The namespace** (`notes/walfs-ext-plan.md`; the paths and the log are `Names.lean`). The
*roots* (`OsState.roots`) name distinct directories of one local filesystem (one journal: the
same `st_dev`), mounted without `nobarrier` and without `journal_async_commit`, with no
case-insensitive (casefold) directory, none in another's tree, every entry in their trees a
regular file or a directory (no symlink, mount point, device, FIFO or socket) and no file a hard
link of another, and no other process changes their trees or moves a directory above a root (a root names one directory
throughout); the filesystem is never read-only and has no error or shutdown event (ext4's
`errors=remount-ro` after a detected inconsistency, an xfs shutdown: then an `fsync` may return 0
without committing); the namespace of the state at boot (`ns`) is their trees' entries, and the
paths in the domain of `files` that are not keys of the namespace's files (`IsInoKey`) resolve to
files outside the roots' trees (not only textually: through the working directory, `..` and
symlinked ancestors too). The filesystem is ext4 (`data=ordered` or `data=journal`, with the
journal, without `fast_commit`) or xfs: metadata operations reach the journal in the order they
are made and the journal commits in order, and an `fsync` of a directory commits it up to the
last change of that directory's entries (N1). Paths in the roots' trees are resolved by the
namespace; any other path, as before, is one of the domain of `files` or the step is stuck.

**Soundness discipline.** The model is never more defined than Linux:
* *Misuse is stuck* (D6): a closed, forged or wrong-mode fd, an unsupported flag, `PROT_WRITE`,
  a nonzero `mmap` offset, a `munmap` of anything but a whole mapping, a negative offset.
* *Environmental failure is a nondeterministic errno*: every operation that makes a system call
  may fail with any nonzero errno. On failure, `Open`, `ftruncate` and `Munmap` may or may not
  have had their effect; a failed `pread` read a prefix; a failed `pwrite` wrote a prefix (as
  `generic_perform_write` does, and Go's loop reports); a failed `fsync` loses the
  writeback of the dirty bytes, which later syncs do not redo (D2).
* *Races*: a change to a file's bytes or size (`pwrite`, `ftruncate`, `fallocate`) is two steps
  (`PWriteStart`/`PWriteFinish`, `FtruncateStart`/`FtruncateFinish`, `FallocStart`/`FallocFinish`), and between them any
  mapped load that could see part of it is stuck (a hole), so a real overlap in time is a stuck
  model interleaving, while a racing `pread` or `fstat` returns any mix (`ReadSees`,
  `StatSees`). A write of `n` bytes at `off` *affects* `[min off size, off + n)`,
  including the zero gap an extending write creates; a truncate affects every byte from
  `min size sz` on, and excludes every other change to the file (`Affects`).
* *Mappings are not read-only in the model, and need not be*: a mapped cell is an ordinary
  byte cell (`Free`), so the model lets a store or CAS on it succeed (until the next step of
  the extension renders the file over it). On Linux, any store or `LOCK CMPXCHG` (even a
  failing one) on a `PROT_READ` page is a SIGSEGV, which Go's runtime turns into a fatal error
  (`unexpected fault address`), not a panic: the process dies. As for out-of-memory
  (`AllocOOMS`), a fatal error only asks the model to contain the run up to it: the adequacy
  theorems claim nothing of a run that dies (no panic fires, the postcondition holds if `main`
  returns), and crash adequacy covers the restart, since a process death is a crash at that
  step: the kernel survives the process, so its page cache, written back later, is what the
  files then hold, and those contents are always a `CrashImage`. The model's extra behaviours
  after such a store are never Go's. This rests on the fault being fatal:
  `runtime/debug.SetPanicOnFault(true)` would make it a recoverable panic, and Perennial does
  not model `runtime/debug` (calling it is stuck).
* *Holes*: a mapped cell past EOF, or affected by an in-flight change, holds `osHole`
  (`LitV LitPoison`, by construction never a byte), so a Go load of it is stuck (SIGBUS, or a
  mix of old and new bytes): less defined than Linux, which is sound. Go's loads of plain
  memory decode bytes (`LoadBytes`), which a hole is not. A raw `Load` of a hole would succeed,
  but goosed code reaches mapped memory only through plain pointers, whose loads are byte
  loads, since a conversion to a non-plain pointer type is stuck. The extension relies on no
  other rule of the core semantics.

**Heap.** The operations never touch user memory: the models pass buffers as Go strings. The
one heap rule is `HeapRendered`, applied by every step: the cells of every mapping after the
step show the file (`cellVal`), the cells of a removed mapping are gone, and every other cell is
unchanged.

**Crash** (`OsCrash`): fds, in-flight changes and mappings are gone (the heap is arbitrary
anyway); each file becomes a crash image (`CrashImage`): a file created since boot may vanish
(D4); the size is one the file had since its last successful sync, or that an in-flight change
would give it; a byte is the durable one unless it is dirty, lost by a failed sync, in-flight, or
past the durable image, when it is arbitrary (D1). The namespace becomes the durable one with a
prefix of the operations since replayed (`NsCrash`, N1), and every file it names survives.
-/
module

public import GooseLang.Ext.OsFs.Names

@[expose] public section

namespace Perennial

/-! ## State -/

/-- A regular file. -/
structure OsFile where
  /-- The page cache: what reads, `fstat` and the mappings see. Its length is the size. -/
  cur : List w8
  /-- The image on disk, as of the last successful sync. -/
  durable : List w8
  /-- The offsets whose durable byte may differ from `cur`'s. -/
  dirty : Nat → Bool
  /-- The smallest and largest sizes since the last successful sync (including then). -/
  sizeLo : Nat
  sizeHi : Nat
  /-- The offsets whose writeback a failed sync lost (D2): the page cache still shows them, the
  disk may not, and Linux marked them clean, so no later sync writes them unless they are written
  again. -/
  lost : Nat → Bool
  /-- The directory entry is durable: false for a file created since boot (D4). -/
  named : Bool

/-- A file as a boot finds it: on disk, all of it durable. -/
def OsFile.ofDisk (img : List w8) : OsFile :=
  { cur := img, durable := img, dirty := fun _ => false, sizeLo := img.length,
    sizeHi := img.length, lost := fun _ => false, named := true }

/-- An open file description: its path and access mode. -/
structure OsFd where
  path : GoString
  readable : Bool
  writable : Bool

/-- What an in-flight change does: a `pwrite` of `data` at `off`, or an `ftruncate` to `sz`. -/
inductive OsChangeKind where
  | write (off : Nat) (data : List w8)
  | truncate (sz : Nat)

/-- A change between its two steps: a `pwrite` or an `ftruncate` of the file at `path`. -/
structure OsChange where
  path : GoString
  kind : OsChangeKind

/-- A mapping: the file's path and the length in bytes. -/
structure OsMap where
  path : GoString
  len : Nat

/-- Where a directory fd's `Readdirnames` is: not begun; begun, with the names (last
components) that were there when it began and that no operation has touched since
(`untouched`), the names there at some point since it began (`seen`), and those it has returned
(`returned`); or done (a second read of the fd is stuck). -/
inductive OsDirRead where
  | idle
  | reading (untouched seen returned : GoString → Bool)
  | done

/-- An open directory: its path when opened (a directory with an open fd is never moved or
removed: the steps that would are stuck), and its read. -/
structure OsDirFd where
  path : GoString
  rd : OsDirRead

/-- The files, fds, in-flight changes and mappings of a node, and its namespace. -/
structure OsState where
  /-- The allowed paths (the domain), and their files (`none`: no such file); and the keys of
  the namespace's files (`IsInoKey`). -/
  files : GMap GoString (Option OsFile)
  fds : GMap w64 OsFd
  /-- In-flight changes, by the token their first step returned (`osTokV`). -/
  inflight : GMap Nat OsChange
  /-- Mappings, by base address. -/
  maps : GMap Loc OsMap
  /-- The roots of the namespace: directories fixed at boot. -/
  roots : List GoString := []
  /-- The namespace: every path in a root's tree that exists. -/
  ns : NsMap := ∅
  /-- The namespace as of the last commit of the journal known to the model. -/
  nsDur : NsMap := ∅
  /-- The metadata operations since, in order: `ns` is them replayed on `nsDur`. -/
  nsLog : List NsOp := []
  /-- Directory fds. Their numbers are distinct from `fds`'s. -/
  dfds : GMap w64 OsDirFd := ∅
  /-- A system call that changes the namespace is between its start (`NsBegin`) and its step. -/
  nsBusy : Bool := false

instance : Inhabited OsState := ⟨{ files := ∅, fds := ∅, inflight := ∅, maps := ∅ }⟩

/-- The Linux file extension. Its values are the tokens of in-flight changes; it has no global
state. -/
@[reducible] def osFsExt : GooseExt where
  name := "os"
  Val := Nat
  LocalState := OsState
  GlobalState := Unit

/-! ## Constants (linux/amd64) -/

def O_RDONLY : Nat := 0x0
def O_WRONLY : Nat := 0x1
def O_RDWR : Nat := 0x2
def O_CREAT : Nat := 0x40
def O_TRUNC : Nat := 0x200
def O_CLOEXEC : Nat := 0x80000
/-- `EINTR` on linux/amd64. -/
def EINTR : w64 := 4
def PROT_READ : Nat := 0x1
def MAP_SHARED : Nat := 0x1
def MAP_POPULATE : Nat := 0x8000
def osPageSize : Nat := 4096

/-! ## Bytes -/

/-- `cur` resized to `sz`: cut, or extended with zeros (`ftruncate`). -/
def resizeBytes (cur : List w8) (sz : Nat) : List w8 :=
  cur.take sz ++ List.replicate (sz - cur.length) 0

/-- `cur` with `d` written at `off`, zero-filling any gap past the end (`pwrite`). Writing
nothing changes nothing, even past the end. -/
def writeBytes (cur : List w8) (off : Nat) (d : List w8) : List w8 :=
  if d = [] then cur
  else
    let c := resizeBytes cur (max cur.length off)
    c.take off ++ d ++ c.drop (off + d.length)

/-- `i` is in `[lo, hi)`. -/
def inRange (lo hi i : Nat) : Bool := lo ≤ i && i < hi

/-! ## Derived facts about a state -/

section derived
variable (st : OsState)

/-- The file at `p`, if `p` is allowed and the file exists. -/
def OsState.file (p : GoString) : Option OsFile := (st.files !! p).bind id

/-- The size of the file at `p` (0 if absent). -/
def OsState.size (p : GoString) : Nat := ((st.file p).map (·.cur.length)).getD 0

/-- The in-flight change `c` may change byte `i` of its file: a write, the bytes it writes and
the zero gap before them; a truncate, every byte from where the old and new sizes part. -/
def Affects (c : OsChange) (i : Nat) : Prop :=
  match c.kind with
  | .write off data => inRange (min off (st.size c.path)) (off + data.length) i
  | .truncate sz => min (st.size c.path) sz ≤ i

/-- The size the change `c` leaves its file: a write's end if it extends the file, the size
otherwise; a truncate's new size. -/
def OsChange.target (c : OsChange) : Nat :=
  match c.kind with
  | .write off data => max (st.size c.path) (off + data.length)
  | .truncate sz => sz

/-- Some in-flight change may change byte `i` of the file at `p`. -/
def InflightAt (p : GoString) (i : Nat) : Prop :=
  ∃ t c, st.inflight !! t = some c ∧ c.path = p ∧ Affects st c i

/-- Some change is in flight on the file at `p`. -/
def BusyAt (p : GoString) : Prop := ∃ t c, st.inflight !! t = some c ∧ c.path = p

/-- What `fstat` may give as the size of the file at `p`: its size, or, while a change resizes it,
a size between its size and the change's target (an extending write grows it page by page). -/
def StatSees (p : GoString) (sz : Nat) : Prop :=
  sz = st.size p ∨ ∃ t c, st.inflight !! t = some c ∧ c.path = p ∧
    min (st.size p) (c.target st) ≤ sz ∧ sz ≤ max (st.size p) (c.target st)

/-- What a `pread` of `n` bytes at `off` of the file at `p` may return: the bytes up to EOF, for a
size `fstat` could see (`StatSees`: the size, or while a change resizes the file, one between the
size and its target, as the read finds it, page by page); each byte the file's, unless an
in-flight change may change it, when it is arbitrary (Linux returns some mix). -/
def ReadSees (p : GoString) (off n : Nat) (r : List w8) : Prop :=
  (∃ sz, StatSees st p sz ∧ r.length = min n (sz - off)) ∧
  ∀ i (h : i < r.length), ¬ InflightAt st p (off + i) →
    ((st.file p).map (·.cur)).bind (·[off + i]?) = some r[i]

/-- `l` is byte `i` of a mapping of the file at `p`. Mappings are disjoint: each lies in cells
that were free when it was made. -/
def MapsTo (l : Loc) (p : GoString) (i : Nat) : Prop :=
  ∃ base m, st.maps !! base = some m ∧ m.path = p ∧ i < m.len ∧ l = base +ₗ (i : Int)

/-- `l` is a cell of some mapping. -/
def Mapped (l : Loc) : Prop := ∃ p i, MapsTo st l p i

/-- A hole: what a mapped cell holds where a load must be stuck. A literal, not `#()`, so that it
is never a byte whatever the Go context's `intoVal`. -/
def osHole [GooseExts] : val := LitV LitPoison

open Classical in
/-- What byte `i` of a mapping of `p` holds: the file's byte, or a hole (`osHole`) past EOF or
where an in-flight change may be changing it. -/
noncomputable def cellVal [GooseExts] [GoGlobalContext] (p : GoString) (i : Nat) : val :=
  match st.file p with
  | some f => if h : i < f.cur.length then
      (if InflightAt st p i then osHole else LitV (LitByte f.cur[i])) else osHole
  | none => osHole

end derived

/-- The heap after a step from `st` to `st'`: every mapping of `st'` shows its file (a cell
that was already mapped keeps its mode; a new one is an ordinary byte cell, `Free`); a cell
mapped in `st` only is gone; every other cell is unchanged. -/
def HeapRendered [GooseExts] [GoGlobalContext] (st st' : OsState) (h h' : GMap Loc (NonAtomic val)) : Prop :=
  (∀ l p i, MapsTo st' l p i → Mapped st l →
    ∃ m v0, h !! l = some (m, v0) ∧ h' !! l = some (m, cellVal st' p i)) ∧
  (∀ l p i, MapsTo st' l p i → ¬ Mapped st l → h' !! l = some (Free (cellVal st' p i))) ∧
  (∀ l, ¬ Mapped st' l → Mapped st l → h' !! l = none) ∧
  (∀ l, ¬ Mapped st' l → ¬ Mapped st l → h' !! l = h !! l)

/-! ## Effects -/

noncomputable section effects

/-- The file at `p` replaced by `f` (`p` allowed). -/
def OsState.setFile (st : OsState) (p : GoString) (f : OsFile) : OsState :=
  { st with files := <[p := some f]> st.files }

/-- `f` with its contents changed to `c`, the bytes `[lo, hi)` marked dirty. -/
def OsFile.change (f : OsFile) (c : List w8) (lo hi : Nat) : OsFile :=
  { f with
    cur := c
    dirty := fun i => f.dirty i || inRange lo hi i
    sizeLo := min f.sizeLo c.length
    sizeHi := max f.sizeHi c.length }

/-- `f` truncated to `sz` (`ftruncate`, `O_TRUNC`). -/
def OsFile.truncate (f : OsFile) (sz : Nat) : OsFile :=
  f.change (resizeBytes f.cur sz) (min f.cur.length sz) (max f.cur.length sz)

/-- `f` after a successful sync: every dirty byte not under an in-flight change (`busy`) is
written (and so no longer lost), and the size is durable. Bytes under an in-flight change stay
dirty. -/
def OsFile.synced (f : OsFile) (busy : Nat → Prop) [DecidablePred busy] : OsFile :=
  { f with
    durable := (List.range f.cur.length).map (fun i =>
      if (f.dirty i ∧ ¬ busy i) ∨ f.durable.length ≤ i then f.cur.getD i 0
      else f.durable.getD i 0),
    dirty := (fun i => f.dirty i && decide (busy i)),
    lost := (fun i => f.lost i && !(f.dirty i && !decide (busy i))),
    sizeLo := f.cur.length, sizeHi := f.cur.length }

/-- `f` after a failed sync: the writeback of the dirty bytes not under an in-flight change
(`busy`) failed; Linux marks their pages clean, so they are lost (D2). Every other byte, and the
durable image, is unchanged. -/
def OsFile.syncFailed (f : OsFile) (busy : Nat → Prop) [DecidablePred busy] : OsFile :=
  { f with
    dirty := (fun i => f.dirty i && decide (busy i)),
    lost := (fun i => f.lost i || (f.dirty i && !decide (busy i))) }

/-- The effect of opening `p` with `creat`/`trunc` on the files (no fd yet): `none` if the
open cannot succeed (no file and no `O_CREAT`). -/
def openEffect (st : OsState) (p : GoString) (creat trunc : Bool) : Option OsState :=
  match st.file p with
  | some f => some (if trunc then st.setFile p (f.truncate 0) else st)
  | none => if creat then
      some (st.setFile p { OsFile.ofDisk [] with named := false }) else none

/-- A read of the directory `df.path` told of the operation `o`: the names it touches there are no
longer untouched and may be returned again, and those it adds have been seen. -/
def OsDirFd.note (o : NsOp) (df : OsDirFd) : OsDirFd :=
  match df.rd with
  | .reading u s r =>
    let u' : GoString → Bool := fun b => u b && decide (b ∉ o.touched df.path)
    let s' : GoString → Bool := fun b => s b || decide (b ∈ o.adds df.path)
    let r' : GoString → Bool := fun b => r b && decide (b ∉ o.touched df.path)
    { df with rd := OsDirRead.reading u' s' r' }
  | _ => df

/-- `st` after the metadata operation `o`: the namespace changed, `o` logged, the directory reads
told. -/
def OsState.nsDo (st : OsState) (o : NsOp) : OsState :=
  { st with ns := o.apply st.ns, nsLog := st.nsLog ++ [o], dfds := GMap.fmap (·.note o) st.dfds }

/-- `st` with no system call changing the namespace in flight (after one's step). -/
def OsState.nsFree (st : OsState) : OsState := { st with nsBusy := false }

/-- `st` with the first `n` operations of its log committed. -/
def OsState.nsCommit (st : OsState) (n : Nat) : OsState :=
  { st with nsDur := nsReplay (st.nsLog.take n) st.nsDur, nsLog := st.nsLog.drop n }

/-- `p` is a managed path that may be created, renamed or removed: canonical, strictly in a root's
tree. -/
def OsState.NsName (st : OsState) (p : GoString) : Prop := ∃ r ∈ st.roots, CanonBelow r p

/-- `p` is a managed path: a root, or an `NsName`. -/
def OsState.NsPath (st : OsState) (p : GoString) : Prop := p ∈ st.roots ∨ st.NsName p

/-- The directory `p` is in exists in the namespace. -/
def OsState.ParentDir (st : OsState) (p : GoString) : Prop :=
  ∃ d, parentOf p = some d ∧ st.ns !! d = some .dir

/-- A new file of the namespace: empty, not durably named (its name is the namespace's). -/
def nsNewFile : OsFile := { OsFile.ofDisk [] with named := false }

/-- What `NsOpen(p)` does before its fd (`st1`), and what the fd will be on: an existing file
(`some k`, its key; truncated with `trunc`); a new file under a fresh key `k`, with `create p k`
logged (`O_CREAT`, in an existing directory); or a directory (`none`), opened read-only without
`O_CREAT` or `O_TRUNC` (Linux refuses the rest, `EISDIR`). -/
def NsOpenEffect (st : OsState) (p : GoString) (acc : Nat) (creat trunc : Bool) (st1 : OsState)
    (tgt : Option GoString) : Prop :=
  match st.ns !! p with
  | some .dir => acc = O_RDONLY ∧ creat = false ∧ trunc = false ∧ st1 = st ∧ tgt = none
  | some (.file k) => (∃ f, st.file k = some f ∧
      st1 = (if trunc then st.setFile k (f.truncate 0) else st)) ∧ tgt = some k
  | none => creat = true ∧ p ∉ st.roots ∧ st.ParentDir p ∧
      ∃ k, IsInoKey k ∧ k ∉ st.files ∧ st1 = (st.setFile k nsNewFile).nsDo (.create p k) ∧
        tgt = some k

/-- The directory `d` has no entries. -/
def NsEmptyDir (st : OsState) (d : GoString) : Prop :=
  st.ns !! d = some .dir ∧ ∀ b, ¬ entryIn st.ns d b

/-- A `rename(2)` that Linux performs (all else fails): of an existing entry to another name in
an existing directory; a file onto nothing or onto a file (replaced: an fd of the replaced file
keeps it); a directory onto nothing or onto an empty directory (replaced), not into its own
tree. -/
def RenameOk (st : OsState) (s t : GoString) : Prop :=
  s ≠ t ∧ st.ParentDir s ∧ st.ParentDir t ∧
  match st.ns !! s with
  | some (.file _) => st.ns !! t ≠ some .dir
  | some .dir => ¬ IsUnder s t ∧ (st.ns !! t = none ∨ NsEmptyDir st t)
  | none => False

/-- Whether `b` is now a name in the directory `d`: a valid name (a direct entry: a path below `d/b`
is not one of `d`'s names). -/
def nsPresent (st : OsState) (d : GoString) (b : GoString) : Bool :=
  decide (NameOk b) && (st.ns !! (d ++ slashB :: b)).isSome

/-- A directory fd's read, as its next step finds it: begun now if it was not. -/
def OsDirRead.cur (st : OsState) (d : GoString) :
    OsDirRead → Option ((GoString → Bool) × (GoString → Bool) × (GoString → Bool))
  | .idle => some (nsPresent st d, nsPresent st d, fun _ => false)
  | .reading u s r => some (u, s, r)
  | .done => none

end effects

/-! ## The step relation -/

section step
variable [GooseExts] [GoGlobalContext]

/-- The token of an in-flight change, an opaque value of the extension: a program cannot forge
one, and there are always fresh ones. -/
abbrev osTokV (t : Nat) : val := ExtV (extVal osFsExt t)

/-- A result and an errno, as the Go wrapper's models take them apart. -/
abbrev osRes (v : val) (e : w64) : Expr := Val (PairV v (#e))

/-- An open fd and its description. -/
def FdOpen (st : OsState) (fd : w64) (d : OsFd) : Prop := st.fds !! fd = some d

/-- `fd` is free: no fd of a file or of a directory has it. -/
def FdFree (st : OsState) (fd : w64) : Prop :=
  0 ≤ fd.toInt ∧ st.fds !! fd = none ∧ st.dfds !! fd = none

/-- The flags `Open` supports: an access mode and `O_CREAT`, `O_TRUNC`, `O_CLOEXEC`. -/
def OpenFlagsOk (fl : Nat) : Prop :=
  fl % 4 ≠ 3 ∧ fl - fl % 4 ∈ [0, O_CREAT, O_TRUNC, O_CREAT + O_TRUNC, O_CLOEXEC,
    O_CREAT + O_CLOEXEC, O_TRUNC + O_CLOEXEC, O_CREAT + O_TRUNC + O_CLOEXEC]

open Classical in
/-- The steps of the operations; the heap is `HeapRendered` (`OsStep`). Each case is a
disjunction: the success branch and its premises, then the failure branch (any nonzero errno). -/
def IsOsStep (op : String) (v : val) (st : OsState) (e' : Expr) (st' : OsState) : Prop :=
  match op with
  /- `open(p, flags)`: `(#p, #flags) ↦ (#fd, #errno)`. -/
  | "Open" => ∃ (p : GoString) (fl : w64), v = PairV (#p) (#fl) ∧ p ∈ st.files ∧
      OpenFlagsOk fl.toNat ∧
      let acc := fl.toNat % 4
      let creat := fl.toNat / O_CREAT % 2 = 1
      let trunc := fl.toNat / O_TRUNC % 2 = 1
      ((∃ (st1 : OsState) (fd : w64), openEffect st p creat trunc = some st1 ∧ 0 ≤ fd.toInt ∧
          (st.fds !! fd = none ∧ st.dfds !! fd = none) ∧
          st' = { st1 with fds := <[fd := ⟨p, acc ≠ O_WRONLY, acc ≠ O_RDONLY⟩]> st1.fds } ∧
          e' = osRes (#fd) 0) ∨
       (∃ e : w64, e ≠ 0 ∧ e' = osRes (#(-1 : w64)) e ∧
          (st' = st ∨ openEffect st p creat trunc = some st')))
  /- `pread(fd, n, off)`: `(#fd, #off, #n) ↦ (#data, #errno)`. It sees what `ReadSees` allows:
  a racing change makes the bytes it may change arbitrary, not the read stuck (bbolt's `WriteTo`
  copies pages a concurrent writer may be rewriting). On failure, a prefix. -/
  | "PRead" => ∃ (fd off n : w64) (d : OsFd) (r : List w8), v = PairV (#fd) (PairV (#off) (#n)) ∧
      FdOpen st fd d ∧ d.readable ∧ 0 ≤ off.toInt ∧ ReadSees st d.path off.toNat n.toNat r ∧
      st' = st ∧
      (e' = osRes (#r) 0 ∨ ∃ (k : Nat) (e : w64), k ≤ r.length ∧ e ≠ 0 ∧ e' = osRes (#(r.take k)) e)
  /- The first step of `pwrite(fd, data, off)`: `(#fd, #off, #data) ↦ token`. It makes no
  system call and cannot fail. The bytes it may change must be clear of every other change. -/
  | "PWriteStart" => ∃ (fd off : w64) (data : List w8) (d : OsFd) (t : Nat),
      v = PairV (#fd) (PairV (#off) (#data)) ∧ FdOpen st fd d ∧ d.writable ∧ 0 ≤ off.toInt ∧
      (let c : OsChange := ⟨d.path, .write off.toNat data⟩
       (∀ i, Affects st c i → ¬ InflightAt st d.path i) ∧
       st.inflight !! t = none ∧ st' = { st with inflight := <[t := c]> st.inflight }) ∧
      e' = Val (osTokV t)
  /- The second step: `token ↦ (#written, #errno)`. A prefix of the data is written: all of
  it and errno 0, or any prefix and a nonzero errno. -/
  | "PWriteFinish" => ∃ (t : Nat) (p : GoString) (off : Nat) (data : List w8) (f : OsFile)
      (k : Nat) (e : w64), v = osTokV t ∧ st.inflight !! t = some ⟨p, .write off data⟩ ∧
      st.file p = some f ∧ k ≤ data.length ∧ (k = data.length ∧ e = 0 ∨ e ≠ 0) ∧
      (let st1 := { st with inflight := GMap.delete t st.inflight }
       st' = if k = 0 then st1 else
         st1.setFile p (f.change (writeBytes f.cur off (data.take k)) (min off f.cur.length)
           (off + k))) ∧
      e' = osRes (#(W64 k)) e
  /- `fstat(fd)`'s size: `#fd ↦ (#size, #errno)`, as `StatSees` allows. -/
  | "Fstat" => ∃ (fd : w64) (d : OsFd) (sz : Nat), v = #fd ∧ FdOpen st fd d ∧
      StatSees st d.path sz ∧ st' = st ∧
      (e' = osRes (#(W64 sz)) 0 ∨ ∃ e : w64, e ≠ 0 ∧ e' = osRes (#(0 : w64)) e)
  /- The first step of `ftruncate(fd, sz)`: `(#fd, #sz) ↦ token`. It makes no system call
  and cannot fail. No other change may be in flight on the file. -/
  | "FtruncateStart" => ∃ (fd sz : w64) (t : Nat) (d : OsFd), v = PairV (#fd) (#sz) ∧ FdOpen st fd d ∧
      d.writable ∧ 0 ≤ sz.toInt ∧ ¬ BusyAt st d.path ∧ st.inflight !! t = none ∧
      st' = { st with inflight := <[t := ⟨d.path, .truncate sz.toNat⟩]> st.inflight } ∧
      e' = Val (osTokV t)
  /- The second step: `token ↦ #errno`. On failure the file may or may not be resized. -/
  | "FtruncateFinish" => ∃ (t : Nat) (p : GoString) (sz : Nat) (f : OsFile), v = osTokV t ∧
      st.inflight !! t = some ⟨p, .truncate sz⟩ ∧ st.file p = some f ∧
      (let st0 := { st with inflight := GMap.delete t st.inflight }
       let st1 := st0.setFile p (f.truncate sz)
       st' = st1 ∧ e' = Val (#(0 : w64)) ∨
       ∃ e : w64, e ≠ 0 ∧ e' = Val (#e) ∧ (st' = st0 ∨ st' = st1))
  /- `fsync(fd)` and `fdatasync(fd)` alike (D3): `#fd ↦ #errno`. A failure is never `EINTR`:
  `fsync(2)` on a local ext4 or xfs file does not return it (its errors are EIO, ENOSPC, EDQUOT,
  EBADF, EROFS/EINVAL), and Go's `File.Sync` retries `EINTR`, so a hidden failed attempt that
  lost pages behind a successful `Sync` would be a run Linux does not have. -/
  | "Fsync" => ∃ (fd : w64) (d : OsFd) (f : OsFile), v = #fd ∧ FdOpen st fd d ∧ st.file d.path = some f ∧
      (st' = st.setFile d.path (f.synced (InflightAt st d.path ·)) ∧ e' = Val (#(0 : w64)) ∨
       ∃ e : w64, e ≠ 0 ∧ e ≠ EINTR ∧ e' = Val (#e) ∧
         st' = st.setFile d.path (f.syncFailed (InflightAt st d.path ·)))
  /- `flock(fd, how)`: `(#fd, #how) ↦ #errno`. Trivial (D7): the lock state is not modelled, so
  the errno is anything (a lock held elsewhere, EINTR, ...); only the fd must be open. -/
  | "Flock" => ∃ (fd how e : w64) (d : OsFd), v = PairV (#fd) (#how) ∧ FdOpen st fd d ∧
      st' = st ∧ e' = Val (#e)
  /- `close(fd)`: `#fd ↦ #errno`. The fd is freed whatever the errno. -/
  | "Close" => ∃ (fd e : w64) (d : OsFd), v = #fd ∧ FdOpen st fd d ∧
      st' = { st with fds := GMap.delete fd st.fds } ∧ e' = Val (#e)
  /- `mmap(nil, len, prot, flags, fd, off)`: `(#fd, #off, #len, #prot, #flags) ↦ (#base, #errno)`.
  The cells are fresh and page-aligned; `HeapRendered` creates them. -/
  | "Mmap" => ∃ (fd off len prot fl : w64) (d : OsFd),
      v = PairV (#fd) (PairV (#off) (PairV (#len) (PairV (#prot) (#fl)))) ∧
      FdOpen st fd d ∧ d.readable ∧ off = 0 ∧ 0 < len.toInt ∧ prot.toNat = PROT_READ ∧
      (fl.toNat = MAP_SHARED ∨ fl.toNat = MAP_SHARED + MAP_POPULATE) ∧ ¬ BusyAt st d.path ∧
      ((∃ base : Loc, 0 < base.addr ∧ (osPageSize : Int) ∣ base.addr ∧
          st.maps !! base = none ∧
          st' = { st with maps := <[base := ⟨d.path, len.toNat⟩]> st.maps } ∧
          e' = osRes (#base) 0) ∨
       (∃ e : w64, e ≠ 0 ∧ st' = st ∧ e' = osRes (#null) e))
  /- `munmap` of a whole mapping, as Go's `unix.Munmap(b)` takes it: `(#ptr, #len, #cap) ↦ #errno`. -/
  | "Munmap" => ∃ (base : Loc) (len cap : w64) (m : OsMap), v = PairV (#base) (PairV (#len) (#cap)) ∧
      st.maps !! base = some m ∧ len.toNat = m.len ∧ cap.toNat = m.len ∧
      let st1 := { st with maps := GMap.delete base st.maps }
      (st' = st1 ∧ e' = Val (#(0 : w64)) ∨
       ∃ e : w64, e ≠ 0 ∧ e' = Val (#e) ∧ (st' = st ∨ st' = st1))
  /- The namespace (`notes/walfs-ext-plan.md`). -/
  /- Which regime `p` is in: `#p ↦ #0` for a path of the domain of `files` (`Open`), `#1`
  otherwise (`NsOpen`). A query of the model, not a system call: `os.OpenFile`'s model asks it
  to choose the step that opens `p`. -/
  | "Regime" => ∃ p : GoString, v = #p ∧ st' = st ∧
      e' = Val (#(if p ∈ st.files then (0 : w64) else 1))
  /- What `fd` is: `#fd ↦ #0` for a file's fd, `#1` for a directory's; stuck on any other. A
  query of the model, not a system call (`File.Sync`'s and `File.Close`'s models ask it). -/
  | "FdKind" => ∃ fd : w64, v = #fd ∧ st' = st ∧
      ((∃ d, st.fds !! fd = some d) ∧ e' = Val (#(0 : w64)) ∨
       st.fds !! fd = none ∧ (∃ df, st.dfds !! fd = some df) ∧ e' = Val (#(1 : w64)))
  /- The start of a system call that changes the namespace (`creat`/`open` with `O_CREAT`,
  `rename`, `unlink`, `rmdir`, `mkdir`): `#() ↦ #()`. Stuck while another one is between its start
  and its step, so that two such calls of the model never overlap in time (N1's order: of two
  calls that do not overlap, the journal has the earlier one first; of two that overlap, it may
  have either first, which the model does not contain, so it is stuck there; the trusted models
  make it just before the call). Not a system call. -/
  | "NsBegin" => v = #() ∧ st.nsBusy = false ∧ st' = { st with nsBusy := true } ∧ e' = Val (#())
  /- `open(p, flags)` of a managed path: `(#p, #flags) ↦ (#fd, #errno)`, as `NsOpenEffect`
  says, with a fresh fd (of a file, on its key, or of a directory). On failure, the effect may or
  may not have happened, without the fd. With `O_CREAT`, after `NsBegin` (it may create). -/
  | "NsOpen" => ∃ (p : GoString) (fl : w64), v = PairV (#p) (#fl) ∧ st.NsPath p ∧
      OpenFlagsOk fl.toNat ∧
      let acc := fl.toNat % 4
      let creat := decide (fl.toNat / O_CREAT % 2 = 1)
      let trunc := decide (fl.toNat / O_TRUNC % 2 = 1)
      let st0 := if creat then st.nsFree else st
      (creat = true → st.nsBusy = true) ∧
      ((∃ (st1 : OsState) (tgt : Option GoString) (fd : w64),
          NsOpenEffect st0 p acc creat trunc st1 tgt ∧ FdFree st fd ∧
          st' = (match tgt with
            | some k => { st1 with fds := <[fd := ⟨k, acc ≠ O_WRONLY, acc ≠ O_RDONLY⟩]> st1.fds }
            | none => { st1 with dfds := <[fd := ⟨p, .idle⟩]> st1.dfds }) ∧
          e' = osRes (#fd) 0) ∨
       (∃ e : w64, e ≠ 0 ∧ e' = osRes (#(-1 : w64)) e ∧
          (st' = st0 ∨ ∃ tgt, NsOpenEffect st0 p acc creat trunc st' tgt)))
  /- `fsync(fd)` of a directory: `#fd ↦ #errno`. Success commits the log up to the last
  operation that changed the directory's entries (`dirCommitLen`: nothing while the log holds an
  operation that made, removed or moved the directory's path or one above it, as the path may then
  have named another directory when an operation was logged); a failure may have committed any
  part of that. -/
  | "DirSync" => ∃ (fd : w64) (df : OsDirFd) (n : Nat), v = #fd ∧ st.dfds !! fd = some df ∧
      n ≤ dirCommitLen df.path st.nsLog ∧ st' = st.nsCommit n ∧
      (n = dirCommitLen df.path st.nsLog ∧ e' = Val (#(0 : w64)) ∨
       ∃ e : w64, e ≠ 0 ∧ e' = Val (#e))
  /- `close(fd)` of a directory: `#fd ↦ #errno`; the fd is freed whatever the errno. -/
  | "DirClose" => ∃ (fd e : w64) (df : OsDirFd), v = #fd ∧ st.dfds !! fd = some df ∧
      st' = { st with dfds := GMap.delete fd st.dfds } ∧ e' = Val (#e)
  /- One step of `Readdirnames(-1)` on a directory fd: `#fd ↦ (#name, #done, #errno)`. A name
  that the directory had at some point since the read began, not returned since it was last
  touched (an entry changed meanwhile may come back, at its new place in the directory); or the
  end, once it has returned every name the directory had when the read began, still has, and that
  no operation touched since (POSIX's `readdir`: an entry added or removed meanwhile may or may
  not be returned); or an errno, the read unchanged. After the end, a second read is stuck. -/
  | "DirReadNext" => ∃ (fd : w64) (df : OsDirFd) (u s r : GoString → Bool), v = #fd ∧
      st.dfds !! fd = some df ∧ df.rd.cur st df.path = some (u, s, r) ∧
      ((∃ b, s b = true ∧ r b = false ∧
          st' = { st with dfds := <[fd := { df with
            rd := .reading u s (fun x => r x || decide (x = b)) }]> st.dfds } ∧
          e' = Val (PairV (#b) (PairV (#(0 : w64)) (#(0 : w64))))) ∨
       ((∀ b, u b = true → nsPresent st df.path b = true → r b = true) ∧
          st' = { st with dfds := <[fd := { df with rd := .done }]> st.dfds } ∧
          e' = Val (PairV (#([] : GoString)) (PairV (#(1 : w64)) (#(0 : w64))))) ∨
       (∃ e : w64, e ≠ 0 ∧
          st' = { st with dfds := <[fd := { df with rd := .reading u s r }]> st.dfds } ∧
          e' = Val (PairV (#([] : GoString)) (PairV (#(0 : w64)) (#e)))))
  /- `lstat(p)`'s "is it a directory", as `os.Rename` asks it of its destination:
  `#p ↦ (#isDir, #errno)`. `#1` only for a directory of the namespace, with a nonzero errno, the
  one `os.Rename` returns then (`EEXIST`, or that of its `lstat` of the source); `#0` otherwise,
  and for a directory too (the `lstat` failed: `Rename`'s model then goes on to `rename(2)`, as
  Go does). -/
  | "NsLstatDir" => ∃ (p : GoString) (isDir e : w64), v = #p ∧ st.NsPath p ∧ st' = st ∧
      (st.ns !! p = some .dir ∧ isDir = 1 ∧ e ≠ 0 ∨ isDir = 0) ∧
      e' = Val (PairV (#isDir) (#e))
  /- `rename(2)` of managed paths, after `NsBegin`: `(#s, #t) ↦ #errno`. As `RenameOk` says, or a
  no-op on an entry renamed to itself; any case may fail, a failure with or without the effect.
  Stuck while a directory fd is open on `t`, or, for a directory `s`, in `s`'s tree. -/
  | "Rename" => ∃ s t : GoString, v = PairV (#s) (#t) ∧ st.NsName s ∧ st.NsName t ∧
      st.nsBusy = true ∧
      (∀ fd df, st.dfds !! fd = some df →
        (st.ns !! s = some .dir → ¬ IsUnder s df.path) ∧ df.path ≠ t) ∧
      ((RenameOk st s t ∧ (st' = st.nsFree.nsDo (.rename s t) ∧ e' = Val (#(0 : w64)) ∨
          ∃ e : w64, e ≠ 0 ∧ e' = Val (#e) ∧
            (st' = st.nsFree ∨ st' = st.nsFree.nsDo (.rename s t)))) ∨
       (s = t ∧ st.ns !! s ≠ none ∧ st' = st.nsFree ∧ e' = Val (#(0 : w64))) ∨
       (∃ e : w64, e ≠ 0 ∧ e' = Val (#e) ∧ st' = st.nsFree))
  /- `unlink(2)` of a managed path, after `NsBegin`: `#p ↦ #errno`. A file is removed (its fds
  keep it); any case may fail, a failure with or without the effect. -/
  | "Unlink" => ∃ p : GoString, v = #p ∧ st.NsName p ∧ st.nsBusy = true ∧
      (((∃ k, st.ns !! p = some (.file k)) ∧
          (st' = st.nsFree.nsDo (.remove p) ∧ e' = Val (#(0 : w64)) ∨
          ∃ e : w64, e ≠ 0 ∧ e' = Val (#e) ∧
            (st' = st.nsFree ∨ st' = st.nsFree.nsDo (.remove p)))) ∨
       (∃ e : w64, e ≠ 0 ∧ e' = Val (#e) ∧ st' = st.nsFree))
  /- `rmdir(2)` of a managed path, after `NsBegin`: `#p ↦ #errno`. An empty directory is removed;
  any case may fail, a failure with or without the effect. Stuck while a directory fd is open on
  `p`. -/
  | "Rmdir" => ∃ p : GoString, v = #p ∧ st.NsName p ∧ st.nsBusy = true ∧
      (∀ fd df, st.dfds !! fd = some df → df.path ≠ p) ∧
      ((NsEmptyDir st p ∧ (st' = st.nsFree.nsDo (.remove p) ∧ e' = Val (#(0 : w64)) ∨
          ∃ e : w64, e ≠ 0 ∧ e' = Val (#e) ∧
            (st' = st.nsFree ∨ st' = st.nsFree.nsDo (.remove p)))) ∨
       (∃ e : w64, e ≠ 0 ∧ e' = Val (#e) ∧ st' = st.nsFree))
  /- `mkdir(2)` of a managed path, after `NsBegin`: `#p ↦ #errno`. A new directory where nothing
  is, in an existing directory; any case may fail, a failure with or without the effect. -/
  | "Mkdir" => ∃ p : GoString, v = #p ∧ st.NsName p ∧ st.nsBusy = true ∧
      ((st.ns !! p = none ∧ st.ParentDir p ∧
          (st' = st.nsFree.nsDo (.mkdir p) ∧ e' = Val (#(0 : w64)) ∨
          ∃ e : w64, e ≠ 0 ∧ e' = Val (#e) ∧
            (st' = st.nsFree ∨ st' = st.nsFree.nsDo (.mkdir p)))) ∨
       (∃ e : w64, e ≠ 0 ∧ e' = Val (#e) ∧ st' = st.nsFree))
  /- The first step of `fallocate(fd, 0, off, len)`: `(#fd, #off, #len) ↦ token`, a truncate
  to `max size (off + len)` in flight, finished by `FallocFinish` (fallocate's visible effect is
  ftruncate's to that size: zeros past the end; the blocks it allocates are not modelled). As
  `FtruncateStart`: no other change may be in flight on the file. Stuck on a negative offset or a
  length not above 0 (Linux: `EINVAL`, after the fd's checks). -/
  | "FallocStart" => ∃ (fd off len : w64) (t : Nat) (d : OsFd),
      v = PairV (#fd) (PairV (#off) (#len)) ∧ FdOpen st fd d ∧ d.writable ∧ 0 ≤ off.toInt ∧
      0 < len.toInt ∧ ¬ BusyAt st d.path ∧ st.inflight !! t = none ∧
      st' = { st with inflight := <[t := ⟨d.path,
        .truncate (max (st.size d.path) (off.toNat + len.toNat))⟩]> st.inflight } ∧
      e' = Val (osTokV t)
  /- The second step: `token ↦ #errno`. On failure the file may have grown to any size between
  its size and the target, zero-filled (ext4 grows it as each chunk is allocated, so `ENOSPC` part
  way leaves it between). -/
  | "FallocFinish" => ∃ (t : Nat) (p : GoString) (sz : Nat) (f : OsFile), v = osTokV t ∧
      st.inflight !! t = some ⟨p, .truncate sz⟩ ∧ st.file p = some f ∧
      (let st0 := { st with inflight := GMap.delete t st.inflight }
       st' = st0.setFile p (f.truncate sz) ∧ e' = Val (#(0 : w64)) ∨
       ∃ e : w64, e ≠ 0 ∧ e' = Val (#e) ∧
         (st' = st0 ∨ ∃ sz', f.cur.length ≤ sz' ∧ sz' ≤ sz ∧ st' = st0.setFile p (f.truncate sz')))
  /- `fallocate(fd, FALLOC_FL_KEEP_SIZE, off, len)`: `(#fd, #off, #len) ↦ #errno`. No visible
  change (it allocates blocks, which are not modelled); any errno. Stuck on a negative offset or
  a length not above 0. -/
  | "FallocKeep" => ∃ (fd off len e : w64) (d : OsFd), v = PairV (#fd) (PairV (#off) (#len)) ∧
      FdOpen st fd d ∧ d.writable ∧ 0 ≤ off.toInt ∧ 0 < len.toInt ∧ st' = st ∧ e' = Val (#e)
  /- `fcntl(fd, F_OFD_SETLK[W], ...)`: `(#fd, #cmd) ↦ #errno`. Trivial, as `Flock` (D7): the lock
  state is not modelled, so the errno is anything. -/
  | "OfdLock" => ∃ (fd cmd e : w64) (d : OsFd), v = PairV (#fd) (#cmd) ∧ FdOpen st fd d ∧
      st' = st ∧ e' = Val (#e)
  | _ => False

/-- The cells a new mapping takes are free, in `(0, maxAddr]`. -/
def MapsFresh (st st' : OsState) (h : GMap Loc (NonAtomic val)) : Prop :=
  ∀ base m, st'.maps !! base = some m → st.maps !! base = none →
    base.addr + m.len ≤ maxAddr ∧ ∀ k < m.len, h !! (base +ₗ (k : Int)) = none

/-- The step relation: an operation's step, the heap rendered from the new state. -/
def OsStep (op : String) (v : val) (h : GMap Loc (NonAtomic val)) (st : OsState) (_g : Unit)
    (e' : Expr) (h' : GMap Loc (NonAtomic val)) (st' : OsState) (_g' : Unit) : Prop :=
  IsOsStep op v st e' st' ∧ MapsFresh st st' h ∧ HeapRendered st st' h h'

end step

/-! ## Crash -/

/-- `img` is what a crash may leave of the file `f` at `p`: a size it had since its last
successful sync, or between such a size and one an in-flight change would give it; a byte is the
durable one unless it is dirty, lost by a failed sync, under an in-flight change, or past the
durable image. -/
def CrashImage (st : OsState) (p : GoString) (f : OsFile) (img : List w8) : Prop :=
  ((f.sizeLo ≤ img.length ∨
      ∃ t c, st.inflight !! t = some c ∧ c.path = p ∧ c.target st ≤ img.length) ∧
     (img.length ≤ f.sizeHi ∨
      ∃ t c, st.inflight !! t = some c ∧ c.path = p ∧ img.length ≤ c.target st)) ∧
  ∀ i (hi : i < img.length), ¬ f.dirty i → ¬ f.lost i → ¬ InflightAt st p i →
    (hd : i < f.durable.length) → img[i] = f.durable[i]

/-- A crash of the files: fds, in-flight changes and mappings are gone; each file becomes a crash
image, as on disk at the next boot, or vanishes if it was created since boot. -/
def OsCrashFiles (st st' : OsState) : Prop :=
  st'.fds = ∅ ∧ st'.inflight = ∅ ∧ st'.maps = ∅ ∧
  ∀ p, match st.files !! p with
    | none => st'.files !! p = none
    | some none => st'.files !! p = some none
    | some (some f) => (¬ f.named ∧ st'.files !! p = some none) ∨
        ∃ img, CrashImage st p f img ∧ st'.files !! p = some (some (OsFile.ofDisk img))

/-- A root's form: canonical and absolute (`/c₁/…/cₙ`, `n ≥ 1`, each component a valid name: no
`.`, `..`, empty component or trailing `/`), so that textual nesting is nesting and no root is
relative to a working directory. -/
def RootForm (r : GoString) : Prop :=
  ∃ cs, cs ≠ [] ∧ (∀ c ∈ cs, NameOk c) ∧ r = joinPath [] cs

/-- The roots: distinct, canonical, none in another's tree. -/
def RootsOk (roots : List GoString) : Prop :=
  roots.Nodup ∧ ∀ r ∈ roots, RootForm r ∧ ∀ r' ∈ roots, r ≠ r' → ¬ IsUnder r r'

/-- `m` is a namespace over `roots`: each root a directory; every other name canonical in a
root's tree, in a directory of `m`; no file named twice (no hard links). -/
def NsShape (roots : List GoString) (m : NsMap) : Prop :=
  (∀ r ∈ roots, m !! r = some .dir) ∧
  (∀ p x, m !! p = some x → p ∈ roots ∨
    ((∃ r ∈ roots, CanonBelow r p) ∧ ∃ d, parentOf p = some d ∧ m !! d = some .dir)) ∧
  (∀ p q k, m !! p = some (.file k) → m !! q = some (.file k) → p = q)

/-- A namespace the program may start in (with `OsInit`'s files, `Ghost.lean`): no directory fd,
nothing logged, all of it durable; the roots and the namespace well formed; every file it names
a file of `files` under a key (`IsInoKey`); the other paths of `files` outside the roots' trees
(the environment assumptions, the module docstring). -/
def NsInit (st : OsState) : Prop :=
  st.dfds = ∅ ∧ st.nsLog = [] ∧ st.nsDur = st.ns ∧ st.nsBusy = false ∧ RootsOk st.roots ∧
  NsShape st.roots st.ns ∧
  (∀ p k, st.ns !! p = some (.file k) → IsInoKey k ∧ ∃ f, st.files !! k = some (some f)) ∧
  (∀ k, k ∈ st.files → ¬ IsInoKey k → ∀ r ∈ st.roots, ¬ IsUnder r k)

/-- A crash of the namespace (N1): the roots stay, directory fds are gone, and the namespace is
the durable one with a prefix of the operations since replayed, all of it durable; every file it
names survives the crash (`OsCrashFiles` lets a file created since boot vanish: one the
namespace names does not). -/
def NsCrash (st st' : OsState) : Prop :=
  st'.roots = st.roots ∧ st'.dfds = ∅ ∧ st'.nsLog = [] ∧ st'.nsDur = st'.ns ∧
  st'.nsBusy = false ∧
  (∃ n, n ≤ st.nsLog.length ∧ st'.ns = nsReplay (st.nsLog.take n) st.nsDur) ∧
  ∀ p k, st'.ns !! p = some (.file k) → ∃ f, st'.files !! k = some (some f)

/-- A crash: of the files and of the namespace. -/
def OsCrash (st st' : OsState) : Prop := OsCrashFiles st st' ∧ NsCrash st st'

instance osFs_semantics : ExtSemantics osFsExt where
  step := OsStep
  crash := OsCrash

end Perennial
