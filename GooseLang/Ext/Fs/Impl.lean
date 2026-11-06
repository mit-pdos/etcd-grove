/-
The Linux file extension of GooseLang, version 2 [Trusted definitions!]. The design is
`notes/fs-semantics-v2.md`.

A node's files and directories as Linux exposes them to one process: the directory tree under
fixed roots (`Tree.lean`), each file's page cache and what its disk may hold, by 512-byte sectors;
and the process's fds, directory fds, system calls in flight and read-only shared mappings. The
machine's part (`FsState`) survives the process; the process's part (`ProcState`) does not.

**Environment** (hypotheses of the adequacy statement, not of this file). The roots (`FsState.roots`)
name distinct directories of one local filesystem (one journal: the same `st_dev`), ext4
(`data=ordered` or `data=journal`, with the journal, without `fast_commit`) or xfs, mounted without
`nobarrier` and without `journal_async_commit`, with no case-insensitive (casefold) directory, none
in another's tree; every entry in their trees is a regular file or a directory (no symlink, mount
point, device, FIFO or socket) and no file is a hard link of another; no other process changes
their trees or moves a directory above a root; the filesystem is never read-only and has no error
or shutdown event (then an `fsync` may return 0 without committing); the tree at boot is their
trees' entries. Metadata operations reach the journal in the order they are made and the journal
commits in order; an `fsync` of a directory commits it up to the last change of that directory's
entries. The device honours cache flushes, has no media errors, and writes each 512-byte sector
atomically: a crash leaves each sector of a write entirely as it was or entirely as sent (sound for
512n and 4Kn devices alike; it excludes a device whose write damages sectors it was not writing).
**No mixed writeback**: the data a writeback sends never mixes a page's contents before and after
a concurrent write into it (ordinary ext4 and xfs do not promise this: without stable pages a write
may change a page during its DMA; it is assumed, `notes/fs-semantics-v2.md`). **No failed
writeback**: no writeback of a file in the roots' trees fails (the device returns no I/O error, and
writeback never fails to allocate blocks, ext4's "Delayed block allocation failed"): Linux may drop
the page cache's copy of data whose writeback failed, so that reads return the disk's older
contents, which the model does not describe (`notes/axiom-review/fs-v2.md`, F1; the model's failed
`fsync` and lost sectors remain, more behaviours than this assumption leaves). **Durable at first
start**: when the program first starts, the roots' trees and every file in them are durable: nothing
has changed them since their last successful `sync`, `syncfs` or `fsync` (F2). Only paths in the
roots' trees are given a meaning: a step on any other path is stuck.

**Soundness discipline.** The model is never more defined than Linux:
* *Misuse is stuck*: a closed, forged or wrong-mode fd, an unsupported flag, `PROT_WRITE`, a
  nonzero `mmap` offset, a `munmap` of anything but a whole mapping, a negative offset, a path that
  is not canonical in a root's tree.
* *Environmental failure is a nondeterministic errno*: every step that makes a system call may fail
  with any nonzero errno; on failure, the changes listed in each case may or may not have happened;
  a failed `pread` read a prefix; a failed `pwrite` wrote a prefix; a failed `fsync` leaves the
  dirty sectors' writeback undone, and Linux marks them clean, so a later sync does not redo them.
* *Races*: a change to a file's bytes or size (`pwrite`, `ftruncate`, `fallocate`) is two steps
  (`…Start`/`…Finish`, the change in flight between them, `ProcState.inflight`); a mapped load that
  could see part of it is stuck (a hole), a racing `pread` or `fstat` returns any mix, and a crash
  may find any prefix of it landed. Metadata calls overlap freely; a crash keeps a set of them that
  respects the journal's order (`Tree.lean`, `Follows`).
* *Mappings*: a mapped cell is an ordinary byte cell; a store to it succeeds in the model, which on
  Linux is a fatal fault (`PROT_READ`), so the model's extra behaviours there are never Go's (Go's
  runtime makes the fault fatal unless `runtime/debug.SetPanicOnFault`, which Perennial does not
  model). A cell past EOF or under an in-flight change holds a hole (`osHole`), never a byte, so a
  Go load of it is stuck.

**Heap.** The steps never touch user memory except through `HeapRendered`: after every step, the
cells of every mapping show the file; a removed mapping's cells are gone; every other cell is
unchanged.

**Crash** (`OsCrash`): a machine crash, or a restart of the process alone. A machine crash keeps the
durable tree with a set of the metadata operations since replayed (the committed ones, closed under
the journal's order, `Follows`); every file that tree names
becomes a crash image (a size it had since its last successful sync, or one an in-flight change
gives it; each sector one of the versions it had since its last successful sync, or the current one
with part of an in-flight change; the bytes of a sector past the size are those of the chosen version,
not zeros: on ext4 a block's tail past a recovered size may hold data whose size change was lost, and
a later extension shows it, F3); every other file, and the process's state, is gone. A process
restart keeps the machine's state, with each in-flight change landed as some prefix: the page cache
and its dirty sectors survive the process, so a later machine crash may still lose them.
-/
module

public import GooseLang.Ext.Fs.Tree

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

/-! ## State -/

/-- The bytes of one 512-byte sector. -/
abbrev SecBytes := Vector w8 512

/-- A sector of zeros. -/
def zeroSec : SecBytes := Vector.ofFn (fun _ => 0)

/-- A 512-byte sector of a file: every version of its contents since the file's last successful
sync, oldest first, the last one the page cache's (never empty); and the kernel's dirty bit, set by
a change, cleared by a sync (a successful one writes the last version; a failed one does not, and a
later one does not redo it: the sector is *lost*, not dirty with more than one version). -/
structure Sector where
  vers : List SecBytes
  dirty : Bool

/-- The page cache's version of the sector. -/
def Sector.last (s : Sector) : SecBytes := s.vers.getLast?.getD zeroSec

/-- A regular file: its sectors (sector `n` holds bytes `[512 n, 512 (n + 1))`, as zero past the
size), its size, and the smallest and largest sizes since its last successful sync. A sector never
written is a clean sector of zeros (`OsFile.ofBytes`). -/
structure OsFile where
  secs : Nat → Sector
  size : Nat
  sizeLo : Nat
  sizeHi : Nat

/-- Sector `n` of the bytes `c`, zero past their end. -/
def secOf (c : List w8) (n : Nat) : SecBytes := Vector.ofFn (fun j : Fin 512 => c.getD (512 * n + j) 0)

/-- A file of size `sz` whose sector `n` holds `vs n`, all of it on disk (a boot and a crash find
files so; the bytes past the size are whatever the sectors hold). -/
def OsFile.ofDisk (vs : Nat → SecBytes) (sz : Nat) : OsFile :=
  { secs := fun n => ⟨[vs n], false⟩, size := sz, sizeLo := sz, sizeHi := sz }

/-- A file holding `c`, all of it on disk, zero past its end. -/
def OsFile.ofBytes (c : List w8) : OsFile := OsFile.ofDisk (secOf c) c.length

/-- Byte `b` of the page cache's versions of the sectors, past the size too. -/
def OsFile.rawAt (f : OsFile) (b : Nat) : w8 := (f.secs (b / 512)).last.toList.getD (b % 512) 0

/-- What reads, `fstat` and mappings see: the last version of each sector, cut to the size. -/
def OsFile.contents (f : OsFile) : List w8 := (List.range f.size).map f.rawAt

/-- An open file description: its file and access mode. (The file offset of `Seek`/`Write`/`Read`
is the Go model's, `TrustedCode/os.lean`: every step here is positional.) -/
structure OsFd where
  ino : Ino
  readable : Bool
  writable : Bool

/-- What an in-flight change does: a `pwrite` of `data` at `off`, or a resize to `sz` (`ftruncate`,
and `fallocate`'s growth). -/
inductive OsChangeKind where
  | write (off : Nat) (data : List w8)
  | truncate (sz : Nat)

/-- A change between its two steps, of the file `ino`. -/
structure OsChange where
  ino : Ino
  kind : OsChangeKind

/-- A read-only shared mapping: its file and its length in bytes. -/
structure OsMap where
  ino : Ino
  len : Nat

/-- Where a directory fd's `Readdirnames` is: not begun; begun, with the names that were there when
it began and that no operation has touched since (`untouched`), the names there at some point since
it began (`seen`), and those it has returned (`returned`); or done (a second read is stuck). -/
inductive OsDirRead where
  | idle
  | reading (untouched seen returned : GoString → Bool)
  | done

/-- An open directory: its inode (it follows the directory across renames, and outlives its
removal: a removed directory reads as empty), and its read. -/
structure OsDirFd where
  ino : Ino
  rd : OsDirRead

/-- The machine's state: the roots (each a path and its directory's inode); the tree as of the boot
(or the last crash) and the metadata operations since, in the order they took effect (the tree now
is derived: `OsState.tree`); the entries of the log a directory `fsync` made durable (`committed`);
the files; and the next inode number to allocate (every inode in use is below it). A file stays in
`files` after its last name goes (its fds may still use it), until a crash. -/
structure FsState where
  roots : List (GoString × Ino)
  treeDur : Tree
  metaLog : List LogEntry
  committed : Nat → Prop
  files : GMap Ino OsFile
  nextIno : Nat

/-- The process's state: its fds (of files and of directories, with distinct numbers), its changes
in flight (by the token their first step returned, `osTokV`), its mappings (by base address), and
its metadata calls in flight (by the token `MetaBegin` returned: the length of the log when the call
began). The two kinds of token are distinct. -/
structure ProcState where
  fds : GMap w64 OsFd
  dfds : GMap w64 OsDirFd
  inflight : GMap Nat OsChange
  maps : GMap Loc OsMap
  metaCalls : GMap Nat Nat

/-- A process with nothing open or in flight. -/
def ProcState.empty : ProcState :=
  { fds := ∅, dfds := ∅, inflight := ∅, maps := ∅, metaCalls := ∅ }

/-- A node's state: the machine's and the process's. -/
structure OsState where
  fs : FsState
  proc : ProcState

instance : Inhabited OsState :=
  ⟨{ fs := { roots := [], treeDur := ∅, metaLog := [], committed := fun _ => False,
                files := ∅, nextIno := 0 }
     proc := ProcState.empty }⟩

/-- The Linux file extension. Its values are the tokens of in-flight changes; it has no global
state. -/
@[reducible] def fsExt : GooseExt where
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

def EINTR : w64 := 4
def PROT_READ : Nat := 0x1
def MAP_SHARED : Nat := 0x1
def MAP_POPULATE : Nat := 0x8000
def osPageSize : Nat := 4096

/-! ## Bytes -/

/-- `i` is in `[lo, hi)`. -/
def inRange (lo hi i : Nat) : Bool := lo ≤ i && i < hi

/-- Sector `n` meets the bytes `[lo, hi)`. -/
def secHits (lo hi n : Nat) : Bool := lo < 512 * (n + 1) && 512 * n < hi

/-! ## File effects -/

section effects

/-- The contents of `f` resized to `sz`: cut, or extended with what the sectors hold past the size
(zeros, except in a sector a crash left with other bytes there, F3). -/
def OsFile.resized (f : OsFile) (sz : Nat) : List w8 := (List.range sz).map f.rawAt

/-- The contents of `f` with `d` written at `off`, any gap past the end filled as `resized` does.
Writing nothing changes nothing, even past the end. -/
def OsFile.written (f : OsFile) (off : Nat) (d : List w8) : List w8 :=
  if d = [] then f.contents
  else
    let c := f.resized (max f.size (off + d.length))
    c.take off ++ d ++ c.drop (off + d.length)

/-- `f` with its contents changed to `c` by a change of the bytes `[lo, hi)`: each sector those
bytes meet gets the new version and becomes dirty (a lost sector written again is dirty again: the
next sync writes it); the size range widens to `c`'s length. -/
def OsFile.change (f : OsFile) (c : List w8) (lo hi : Nat) : OsFile :=
  { secs := fun n => if secHits lo hi n then ⟨(f.secs n).vers ++ [secOf c n], true⟩ else f.secs n,
    size := c.length,
    sizeLo := min f.sizeLo c.length,
    sizeHi := max f.sizeHi c.length }

/-- `f` with `k` bytes of a `pwrite` of `data` at `off` landed (nothing if `k = 0`): the bytes
`[min off size, off + k)` change, the zero gap before them included. -/
def OsFile.landWrite (f : OsFile) (off : Nat) (data : List w8) (k : Nat) : OsFile :=
  if k = 0 then f
  else f.change (f.written off (data.take k)) (min off f.size) (off + k)

/-- `f` resized to `sz`: every byte from where the old and new sizes part changes. -/
def OsFile.truncate (f : OsFile) (sz : Nat) : OsFile :=
  f.change (f.resized sz) (min f.size sz) (max f.size sz)

/-- `f` after a successful sync: every dirty sector not under an in-flight change (`busy`) is
written, its versions collapsed to the last; a lost one is unchanged (Linux does not write it); the
size is durable. -/
def OsFile.synced (f : OsFile) (busy : Nat → Prop) [DecidablePred busy] : OsFile :=
  { f with
    secs := fun n => let s := f.secs n
      if s.dirty ∧ ¬ busy n then ⟨[s.last], false⟩ else s,
    sizeLo := f.size, sizeHi := f.size }

/-- `f` after a failed sync: the writeback of each dirty sector not under an in-flight change
(`busy`) failed and Linux marks it clean: it is lost, its versions kept. The sizes are unchanged. -/
def OsFile.syncFailed (f : OsFile) (busy : Nat → Prop) [DecidablePred busy] : OsFile :=
  { f with
    secs := fun n => let s := f.secs n
      if s.dirty ∧ ¬ busy n then { s with dirty := false } else s }

/-- `f'` is `f` with each of the changes `ks`, in order, landed as some prefix: some bytes of a
write (possibly none or all), a resize to any size between the file's and its target (ext4 resizes
in chunks, and goes on after the process is killed, F5). -/
inductive Landed : List OsChangeKind → OsFile → OsFile → Prop where
  | nil (f : OsFile) : Landed [] f f
  | write (off : Nat) (data : List w8) (k : Nat) (ks : List OsChangeKind) (f f' : OsFile) :
      k ≤ data.length → Landed ks (f.landWrite off data k) f' →
      Landed (.write off data :: ks) f f'
  | trunc (sz sz' : Nat) (ks : List OsChangeKind) (f f' : OsFile) :
      min f.size sz ≤ sz' → sz' ≤ max f.size sz →
      Landed ks (f.truncate sz') f' → Landed (.truncate sz :: ks) f f'

end effects

/-! ## Derived facts about a state -/

section derived
variable (st : OsState)

/-- The tree now: the durable tree with the operations since replayed. -/
def OsState.tree : Tree := replay (st.fs.metaLog.map (·.op)) st.fs.treeDur

/-- The file of inode `i`. -/
def OsState.file (i : Ino) : Option OsFile := st.fs.files !! i

/-- The size of the file of `i` (0 if there is none). -/
def OsState.size (i : Ino) : Nat := ((st.file i).map (·.size)).getD 0

/-- The in-flight change `c` may change byte `b` of its file: a write, the bytes it writes and the
zero gap before them; a resize, every byte from where the old and new sizes part. -/
def Affects (c : OsChange) (b : Nat) : Prop :=
  match c.kind with
  | .write off data => inRange (min off (st.size c.ino)) (off + data.length) b
  | .truncate sz => min (st.size c.ino) sz ≤ b

/-- The size the change `c` leaves its file. -/
def OsChange.target (c : OsChange) : Nat :=
  match c.kind with
  | .write off data => max (st.size c.ino) (off + data.length)
  | .truncate sz => sz

/-- Some in-flight change may change byte `b` of the file of `i`. -/
def InflightAt (i : Ino) (b : Nat) : Prop :=
  ∃ t c, st.proc.inflight !! t = some c ∧ c.ino = i ∧ Affects st c b

/-- Some in-flight change may change a byte of sector `n` of the file of `i`. -/
def SecBusy (i : Ino) (n : Nat) : Prop :=
  ∃ b, 512 * n ≤ b ∧ b < 512 * (n + 1) ∧ InflightAt st i b

/-- Some change is in flight on the file of `i`. -/
def BusyAt (i : Ino) : Prop := ∃ t c, st.proc.inflight !! t = some c ∧ c.ino = i

/-- The kinds of the changes in flight on the file of `i`. -/
def changesOn (i : Ino) : List OsChangeKind :=
  ((st.proc.inflight.toList.map (·.2)).filter (fun c => decide (c.ino = i))).map (·.kind)

/-- What `fstat` may give as the size of the file of `i`: its size, or, while a change resizes it,
a size between its size and the change's target. -/
def StatSees (i : Ino) (sz : Nat) : Prop :=
  sz = st.size i ∨ ∃ t c, st.proc.inflight !! t = some c ∧ c.ino = i ∧
    min (st.size i) (c.target st) ≤ sz ∧ sz ≤ max (st.size i) (c.target st)

/-- What a `pread` of `n` bytes at `off` of the file of `i` may return: the bytes up to EOF, for a
size `fstat` could see; each byte the file's, unless an in-flight change may change it, when it is
arbitrary (Linux returns some mix). -/
def ReadSees (i : Ino) (off n : Nat) (r : List w8) : Prop :=
  (∃ sz, StatSees st i sz ∧ r.length = min n (sz - off)) ∧
  ∀ j (h : j < r.length), ¬ InflightAt st i (off + j) →
    ((st.file i).map (·.contents)).bind (·[off + j]?) = some r[j]

/-- `l` is byte `b` of a mapping of the file of `i`. Mappings are disjoint: each lies in cells that
were free when it was made. -/
def MapsTo (l : Loc) (i : Ino) (b : Nat) : Prop :=
  ∃ base m, st.proc.maps !! base = some m ∧ m.ino = i ∧ b < m.len ∧ l = base +ₗ (b : Int)

/-- `l` is a cell of some mapping. -/
def Mapped (l : Loc) : Prop := ∃ i b, MapsTo st l i b

/-- A hole: what a mapped cell holds where a load must be stuck. A literal, not `#()`, so that it
is never a byte whatever the Go context's `intoVal`. -/
def osHole [GooseExts] : val := LitV LitPoison

open Classical in
/-- What byte `b` of a mapping of the file of `i` holds: the file's byte, or a hole past EOF or
where an in-flight change may be changing it. -/
noncomputable def cellVal [GooseExts] [GoGlobalContext] (i : Ino) (b : Nat) : val :=
  match st.file i with
  | some f => if h : b < f.contents.length then
      (if InflightAt st i b then osHole else LitV (LitByte f.contents[b])) else osHole
  | none => osHole

end derived

/-- The heap after a step from `st` to `st'`: every mapping of `st'` shows its file (a cell that was
already mapped keeps its mode; a new one is an ordinary byte cell, `Free`); a cell mapped in `st`
only is gone; every other cell is unchanged. -/
def HeapRendered [GooseExts] [GoGlobalContext] (st st' : OsState)
    (h h' : GMap Loc (NonAtomic val)) : Prop :=
  (∀ l i b, MapsTo st' l i b → Mapped st l →
    ∃ m v0, h !! l = some (m, v0) ∧ h' !! l = some (m, cellVal st' i b)) ∧
  (∀ l i b, MapsTo st' l i b → ¬ Mapped st l → h' !! l = some (Free (cellVal st' i b))) ∧
  (∀ l, ¬ Mapped st' l → Mapped st l → h' !! l = none) ∧
  (∀ l, ¬ Mapped st' l → ¬ Mapped st l → h' !! l = h !! l)

/-! ## State effects -/

section effects2

/-- The file of `i` replaced by `f`. -/
def OsState.setFile (st : OsState) (i : Ino) (f : OsFile) : OsState :=
  { st with fs := { st.fs with files := <[i := f]> st.fs.files } }

/-- The process's state replaced. -/
def OsState.setProc (st : OsState) (p : ProcState) : OsState := { st with proc := p }

/-- The node the components `cs` lead to from `n` in `m`. -/
def walk (m : Tree) : Node → List GoString → Option Node
  | n, [] => some n
  | .dir j, c :: cs => match m.entry j c with
    | some n => walk m n cs
    | none => none
  | .file _, _ :: _ => none

open Classical in
/-- What the path `p` names now: a root followed by valid components, walked from the root's
directory (the roots' forms make the split unique: `RootsOk`); nothing for any other path. -/
def OsState.lookup (st : OsState) (p : GoString) : Option Node :=
  if h : ∃ (rj : GoString × Ino) (cs : List GoString), rj ∈ st.fs.roots ∧ (∀ c ∈ cs, NameOk c) ∧
      p = joinPath rj.1 cs then
    walk st.tree (.dir h.choose.2) h.choose_spec.choose
  else none

/-- `p` is a path that may be created, renamed or removed: canonical, strictly in a root's tree. -/
def OsState.TreeName (st : OsState) (p : GoString) : Prop := ∃ rj ∈ st.fs.roots, CanonBelow rj.1 p

/-- `p` is a path of the roots' trees: a root, or a `TreeName`. -/
def OsState.TreePath (st : OsState) (p : GoString) : Prop :=
  (∃ rj ∈ st.fs.roots, rj.1 = p) ∨ st.TreeName p

/-- The directory `p` is in (its inode) and `p`'s last component, if that directory exists. -/
def OsState.parent (st : OsState) (p : GoString) : Option (Ino × GoString) :=
  match parentOf p with
  | some d => match st.lookup d with
    | some (.dir j) => some (j, baseOf p)
    | _ => none
  | none => none

/-- The directory `p` is in exists. -/
def OsState.ParentDir (st : OsState) (p : GoString) : Prop := ∃ jb, st.parent p = some jb

/-- A read of the directory `df.ino` told of the operation `o`: the names it touches there are no
longer untouched and may be returned again, and those it adds have been seen. -/
def OsDirFd.note (o : MetaOp) (df : OsDirFd) : OsDirFd :=
  match df.rd with
  | .reading u s r =>
    let u' : GoString → Bool := fun b => u b && decide (b ∉ o.touched df.ino)
    let s' : GoString → Bool := fun b => s b || decide (b ∈ o.adds df.ino)
    let r' : GoString → Bool := fun b => r b && decide (b ∉ o.touched df.ino)
    { df with rd := OsDirRead.reading u' s' r' }
  | _ => df

/-- `st` with the metadata call `t` done (after its step). -/
def OsState.metaEnd (st : OsState) (t : Nat) : OsState :=
  { st with proc := { st.proc with metaCalls := GMap.delete t st.proc.metaCalls } }

/-- `st` after the metadata operation `o` of a call that began when the log had `start` entries:
`o` logged (the tree now changes with it), the directory reads told. -/
def OsState.metaDo (st : OsState) (o : MetaOp) (start : Nat) : OsState :=
  { fs := { st.fs with metaLog := st.fs.metaLog ++ [⟨o, start⟩] },
    proc := { st.proc with dfds := GMap.fmap (·.note o) st.proc.dfds } }

/-- `st` with the next inode number taken. -/
def OsState.takeIno (st : OsState) : OsState :=
  { st with fs := { st.fs with nextIno := st.fs.nextIno + 1 } }

/-- `st` with the entry `x` of its log, and what it follows, durable. -/
def OsState.commitThrough (st : OsState) (x : Nat) : OsState :=
  { st with fs := { st.fs with committed := fun y => st.fs.committed y ∨ Needed st.fs.metaLog x y } }

/-- A new file: empty. Whether its name survives a crash is the tree's question. -/
def newFile : OsFile := OsFile.ofBytes []

/-- What `open(p)` does before its fd (`st1`), and what the fd will be on (`tgt`): an existing file
(truncated with `trunc`); a new file of a fresh inode, with its `create` logged (`O_CREAT`, in an
existing directory; `start` the call's start); or a directory, opened read-only without `O_CREAT` or
`O_TRUNC` (Linux refuses the rest, `EISDIR`). -/
def OpenEffect (st : OsState) (p : GoString) (acc : Nat) (creat trunc : Bool) (start : Nat)
    (st1 : OsState) (tgt : Node) : Prop :=
  match st.lookup p with
  | some (.dir j) => acc = O_RDONLY ∧ creat = false ∧ trunc = false ∧ st1 = st ∧ tgt = .dir j
  | some (.file i) => (∃ f, st.file i = some f ∧
      st1 = (if trunc then st.setFile i (f.truncate 0) else st)) ∧ tgt = .file i
  | none => creat = true ∧ ∃ j b, st.parent p = some (j, b) ∧
      st1 = ((st.setFile st.fs.nextIno newFile).takeIno).metaDo (.create j b st.fs.nextIno) start ∧
      tgt = .file st.fs.nextIno

/-- The path `p` is an empty directory, of inode `j`. -/
def EmptyDir (st : OsState) (p : GoString) (j : Ino) : Prop :=
  st.lookup p = some (.dir j) ∧ ∀ b, st.tree.entry j b = none

/-- A `rename(2)` that Linux performs (all else fails): of an existing entry to another name in an
existing directory; a file onto nothing or onto a file (replaced: an fd of the replaced file keeps
it); a directory onto nothing or onto an empty directory (replaced), not into its own tree. -/
def RenameOk (st : OsState) (s t : GoString) : Prop :=
  s ≠ t ∧ st.ParentDir s ∧ st.ParentDir t ∧
  match st.lookup s with
  | some (.file _) => ∀ j, st.lookup t ≠ some (.dir j)
  | some (.dir _) => ¬ IsUnder s t ∧ (st.lookup t = none ∨ ∃ j, EmptyDir st t j)
  | none => False

/-- The rename of `s` to `t`, as logged. -/
def RenameOp (st : OsState) (s t : GoString) (o : MetaOp) : Prop :=
  ∃ js bs jt bt n, st.parent s = some (js, bs) ∧ st.parent t = some (jt, bt) ∧
    st.lookup s = some n ∧ o = .rename js bs jt bt n (st.lookup t)

/-- Whether `b` is now a name in the directory `j`. -/
def present (st : OsState) (j : Ino) (b : GoString) : Bool :=
  decide (NameOk b) && (st.tree.entry j b).isSome

/-- A directory fd's read, as its next step finds it: begun now if it was not. -/
def OsDirRead.cur (st : OsState) (j : Ino) :
    OsDirRead → Option ((GoString → Bool) × (GoString → Bool) × (GoString → Bool))
  | .idle => some (present st j, present st j, fun _ => false)
  | .reading u s r => some (u, s, r)
  | .done => none

end effects2

/-! ## The step relation -/

section step
variable [GooseExts] [GoGlobalContext]

/-- The token of an in-flight change, an opaque value of the extension: a program cannot forge one,
and there are always fresh ones. -/
abbrev osTokV (t : Nat) : val := ExtV (extVal fsExt t)

/-- A result and an errno, as the Go wrapper's models take them apart. -/
abbrev osRes (v : val) (e : w64) : Expr := Val (PairV v (#e))

/-- An open fd of a file and its description. -/
def FdOpen (st : OsState) (fd : w64) (d : OsFd) : Prop := st.proc.fds !! fd = some d

/-- `fd` is free: no fd of a file or of a directory has it. -/
def FdFree (st : OsState) (fd : w64) : Prop :=
  0 ≤ fd.toInt ∧ st.proc.fds !! fd = none ∧ st.proc.dfds !! fd = none

/-- The flags `Open` supports: an access mode and `O_CREAT`, `O_TRUNC`, `O_CLOEXEC`. -/
def OpenFlagsOk (fl : Nat) : Prop :=
  fl % 4 ≠ 3 ∧ fl - fl % 4 ∈ [0, O_CREAT, O_TRUNC, O_CREAT + O_TRUNC, O_CLOEXEC,
    O_CREAT + O_CLOEXEC, O_TRUNC + O_CLOEXEC, O_CREAT + O_TRUNC + O_CLOEXEC]

/-- `st` with the in-flight change `t` done. -/
def OsState.doneInflight (st : OsState) (t : Nat) : OsState :=
  { st with proc := { st.proc with inflight := GMap.delete t st.proc.inflight } }

/-- `st` with `c` in flight under the token `t`. -/
def OsState.addInflight (st : OsState) (t : Nat) (c : OsChange) : OsState :=
  { st with proc := { st.proc with inflight := <[t := c]> st.proc.inflight } }

open Classical in
/-- The steps of the operations; the heap is `HeapRendered` (`FsStep`). Each case is a disjunction:
the success branch and its premises, then the failure branch (any nonzero errno). -/
def IsFsStep (op : String) (v : val) (st : OsState) (e' : Expr) (st' : OsState) : Prop :=
  match op with
  /- `open(p, flags)` of a path of the roots' trees: `(tok, #p, #flags) ↦ (#fd, #errno)`, as
  `OpenEffect` says, with a fresh fd (of a file, on its inode, or of a directory, on its inode). On
  failure, the effect may or may not have happened, without the fd. With `O_CREAT` (it may create),
  `tok` is the token of a metadata call (`MetaBegin`), which the step ends; otherwise `#()`. -/
  | "Open" => ∃ (tv : val) (p : GoString) (fl : w64) (t start : Nat),
      v = PairV tv (PairV (#p) (#fl)) ∧ st.TreePath p ∧ OpenFlagsOk fl.toNat ∧
      let acc := fl.toNat % 4
      let creat := decide (fl.toNat / O_CREAT % 2 = 1)
      let trunc := decide (fl.toNat / O_TRUNC % 2 = 1)
      let st0 := if creat then st.metaEnd t else st
      (creat = true → tv = osTokV t ∧ st.proc.metaCalls !! t = some start) ∧
      (creat = false → tv = #()) ∧
      ((∃ (st1 : OsState) (tgt : Node) (fd : w64),
          OpenEffect st0 p acc creat trunc start st1 tgt ∧ FdFree st fd ∧
          st' = (match tgt with
            | .file i => st1.setProc { st1.proc with
                fds := <[fd := ⟨i, acc ≠ O_WRONLY, acc ≠ O_RDONLY⟩]> st1.proc.fds }
            | .dir j => st1.setProc { st1.proc with
                dfds := <[fd := ⟨j, .idle⟩]> st1.proc.dfds }) ∧
          e' = osRes (#fd) 0) ∨
       (∃ e : w64, e ≠ 0 ∧ e' = osRes (#(-1 : w64)) e ∧
          (st' = st0 ∨ ∃ tgt, OpenEffect st0 p acc creat trunc start st' tgt)))
  /- `pread(fd, n, off)`: `(#fd, #off, #n) ↦ (#data, #errno)`, as `ReadSees` allows. On success,
  a non-empty prefix (Linux returns a short count when page allocation fails part way, F4), or
  nothing at EOF; on failure, any prefix. -/
  | "PRead" => ∃ (fd off n : w64) (d : OsFd) (r : List w8), v = PairV (#fd) (PairV (#off) (#n)) ∧
      FdOpen st fd d ∧ d.readable ∧ 0 ≤ off.toInt ∧ ReadSees st d.ino off.toNat n.toNat r ∧
      st' = st ∧
      ((∃ k, k ≤ r.length ∧ (0 < k ∨ r = []) ∧ e' = osRes (#(r.take k)) 0) ∨
       ∃ (k : Nat) (e : w64), k ≤ r.length ∧ e ≠ 0 ∧ e' = osRes (#(r.take k)) e)
  /- The first step of `pwrite(fd, data, off)`: `(#fd, #off, #data) ↦ token`. It makes no system
  call and cannot fail. The bytes it may change must be clear of every other change. -/
  | "PWriteStart" => ∃ (fd off : w64) (data : List w8) (d : OsFd) (t : Nat),
      v = PairV (#fd) (PairV (#off) (#data)) ∧ FdOpen st fd d ∧ d.writable ∧ 0 ≤ off.toInt ∧
      (let c : OsChange := ⟨d.ino, .write off.toNat data⟩
       (∀ b, Affects st c b → ¬ InflightAt st d.ino b) ∧
       st.proc.inflight !! t = none ∧ st.proc.metaCalls !! t = none ∧ st' = st.addInflight t c) ∧
      e' = Val (osTokV t)
  /- The second step: `token ↦ (#written, #errno)`. A prefix of the data is written: with errno
  0, all of it or a non-empty part (a short write, F6); with a nonzero errno, any prefix. -/
  | "PWriteFinish" => ∃ (t : Nat) (i : Ino) (off : Nat) (data : List w8) (f : OsFile)
      (k : Nat) (e : w64), v = osTokV t ∧ st.proc.inflight !! t = some ⟨i, .write off data⟩ ∧
      st.file i = some f ∧ k ≤ data.length ∧ ((k = data.length ∨ 0 < k) ∧ e = 0 ∨ e ≠ 0) ∧
      st' = (st.doneInflight t).setFile i (f.landWrite off data k) ∧
      e' = osRes (#(W64 k)) e
  /- `fstat(fd)`'s size: `#fd ↦ (#size, #errno)`, as `StatSees` allows. -/
  | "Fstat" => ∃ (fd : w64) (d : OsFd) (sz : Nat), v = #fd ∧ FdOpen st fd d ∧
      StatSees st d.ino sz ∧ st' = st ∧
      (e' = osRes (#(W64 sz)) 0 ∨ ∃ e : w64, e ≠ 0 ∧ e' = osRes (#(0 : w64)) e)
  /- The first step of `ftruncate(fd, sz)`: `(#fd, #sz) ↦ token`. It makes no system call and
  cannot fail. No other change may be in flight on the file. -/
  | "FtruncateStart" => ∃ (fd sz : w64) (t : Nat) (d : OsFd), v = PairV (#fd) (#sz) ∧
      FdOpen st fd d ∧ d.writable ∧ 0 ≤ sz.toInt ∧ ¬ BusyAt st d.ino ∧
      st.proc.inflight !! t = none ∧ st.proc.metaCalls !! t = none ∧
      st' = st.addInflight t ⟨d.ino, .truncate sz.toNat⟩ ∧
      e' = Val (osTokV t)
  /- The second step: `token ↦ #errno`. On failure the file may or may not be resized. -/
  | "FtruncateFinish" => ∃ (t : Nat) (i : Ino) (sz : Nat) (f : OsFile), v = osTokV t ∧
      st.proc.inflight !! t = some ⟨i, .truncate sz⟩ ∧ st.file i = some f ∧
      (let st0 := st.doneInflight t
       let st1 := st0.setFile i (f.truncate sz)
       st' = st1 ∧ e' = Val (#(0 : w64)) ∨
       ∃ e : w64, e ≠ 0 ∧ e' = Val (#e) ∧ (st' = st0 ∨ st' = st1))
  /- `fsync(fd)` and `fdatasync(fd)` of a file alike: `#fd ↦ #errno`. A failure is never `EINTR`:
  `fsync(2)` on a local ext4 or xfs file does not return it, and Go's `File.Sync` retries `EINTR`,
  so a hidden failed attempt behind a successful `Sync` would be a run Linux does not have. It
  commits no name. -/
  | "Fsync" => ∃ (fd : w64) (d : OsFd) (f : OsFile), v = #fd ∧ FdOpen st fd d ∧
      st.file d.ino = some f ∧
      (st' = st.setFile d.ino (f.synced (SecBusy st d.ino ·)) ∧ e' = Val (#(0 : w64)) ∨
       ∃ e : w64, e ≠ 0 ∧ e ≠ EINTR ∧ e' = Val (#e) ∧
         st' = st.setFile d.ino (f.syncFailed (SecBusy st d.ino ·)))
  /- `flock(fd, how)`: `(#fd, #how) ↦ #errno`. Trivial: the lock state is not modelled, so the
  errno is anything; only the fd must be open. -/
  | "Flock" => ∃ (fd how e : w64) (d : OsFd), v = PairV (#fd) (#how) ∧ FdOpen st fd d ∧
      st' = st ∧ e' = Val (#e)
  /- `close(fd)` of a file: `#fd ↦ #errno`. The fd is freed whatever the errno. -/
  | "Close" => ∃ (fd e : w64) (d : OsFd), v = #fd ∧ FdOpen st fd d ∧
      st' = st.setProc { st.proc with fds := GMap.delete fd st.proc.fds } ∧ e' = Val (#e)
  /- `mmap(nil, len, prot, flags, fd, off)`: `(#fd, #off, #len, #prot, #flags) ↦ (#base, #errno)`.
  The cells are fresh and page-aligned; `HeapRendered` creates them. -/
  | "Mmap" => ∃ (fd off len prot fl : w64) (d : OsFd),
      v = PairV (#fd) (PairV (#off) (PairV (#len) (PairV (#prot) (#fl)))) ∧
      FdOpen st fd d ∧ d.readable ∧ off = 0 ∧ 0 < len.toInt ∧ prot.toNat = PROT_READ ∧
      (fl.toNat = MAP_SHARED ∨ fl.toNat = MAP_SHARED + MAP_POPULATE) ∧ ¬ BusyAt st d.ino ∧
      ((∃ base : Loc, 0 < base.addr ∧ (osPageSize : Int) ∣ base.addr ∧
          st.proc.maps !! base = none ∧
          st' = st.setProc { st.proc with maps := <[base := ⟨d.ino, len.toNat⟩]> st.proc.maps } ∧
          e' = osRes (#base) 0) ∨
       (∃ e : w64, e ≠ 0 ∧ st' = st ∧ e' = osRes (#null) e))
  /- `munmap` of a whole mapping, as Go's `unix.Munmap(b)` takes it: `(#ptr, #len, #cap) ↦ #errno`. -/
  | "Munmap" => ∃ (base : Loc) (len cap : w64) (m : OsMap),
      v = PairV (#base) (PairV (#len) (#cap)) ∧
      st.proc.maps !! base = some m ∧ len.toNat = m.len ∧ cap.toNat = m.len ∧
      let st1 := st.setProc { st.proc with maps := GMap.delete base st.proc.maps }
      (st' = st1 ∧ e' = Val (#(0 : w64)) ∨
       ∃ e : w64, e ≠ 0 ∧ e' = Val (#e) ∧ (st' = st ∨ st' = st1))
  /- What `fd` is: `#fd ↦ #0` for a file's fd, `#1` for a directory's; stuck on any other. A query
  of the model, not a system call (`File.Sync`'s and `File.Close`'s models ask it). -/
  | "FdKind" => ∃ fd : w64, v = #fd ∧ st' = st ∧
      ((∃ d, st.proc.fds !! fd = some d) ∧ e' = Val (#(0 : w64)) ∨
       st.proc.fds !! fd = none ∧ (∃ df, st.proc.dfds !! fd = some df) ∧ e' = Val (#(1 : w64)))
  /- The start of a system call that changes the tree (`open` with `O_CREAT`, `rename`, `unlink`,
  `rmdir`, `mkdir`): `#() ↦ tok`, a token recording the length of the log now (the operations that
  have taken effect before the call began: the journal has them before it). The trusted models make
  it just before the call. Not a system call; calls overlap freely. -/
  | "MetaBegin" => ∃ t : Nat, v = #() ∧ st.proc.metaCalls !! t = none ∧
      st.proc.inflight !! t = none ∧
      st' = st.setProc { st.proc with metaCalls := <[t := st.fs.metaLog.length]> st.proc.metaCalls } ∧
      e' = Val (osTokV t)
  /- `fsync(fd)` of a directory: `#fd ↦ #errno`. Success makes the last logged operation that
  changed or locked the directory durable, with everything it follows (`Needed`: ext4 commits the
  whole journal, xfs forces its log through the directory's last change); a failure guarantees
  nothing more (whatever it committed, a crash may keep anyway). -/
  | "DirSync" => ∃ (fd : w64) (df : OsDirFd), v = #fd ∧ st.proc.dfds !! fd = some df ∧
      ((st' = (match lastTouch st.fs.metaLog df.ino with
          | some x => st.commitThrough x
          | none => st) ∧ e' = Val (#(0 : w64))) ∨
       ∃ e : w64, e ≠ 0 ∧ e' = Val (#e) ∧ st' = st)
  /- `close(fd)` of a directory: `#fd ↦ #errno`; the fd is freed whatever the errno. -/
  | "DirClose" => ∃ (fd e : w64) (df : OsDirFd), v = #fd ∧ st.proc.dfds !! fd = some df ∧
      st' = st.setProc { st.proc with dfds := GMap.delete fd st.proc.dfds } ∧ e' = Val (#e)
  /- One step of `Readdirnames(-1)` on a directory fd: `#fd ↦ (#name, #done, #errno)`. A name that
  the directory had at some point since the read began, not returned since it was last touched; or
  the end, once it has returned every name the directory had when the read began, still has, and
  that no operation touched since (POSIX's `readdir`: an entry added or removed meanwhile may or may
  not be returned); or an errno, the read unchanged. After the end, a second read is stuck. A
  removed directory has no names. -/
  | "DirReadNext" => ∃ (fd : w64) (df : OsDirFd) (u s r : GoString → Bool), v = #fd ∧
      st.proc.dfds !! fd = some df ∧ df.rd.cur st df.ino = some (u, s, r) ∧
      ((∃ b, s b = true ∧ r b = false ∧
          st' = st.setProc { st.proc with dfds := <[fd := { df with
            rd := .reading u s (fun x => r x || decide (x = b)) }]> st.proc.dfds } ∧
          e' = Val (PairV (#b) (PairV (#(0 : w64)) (#(0 : w64))))) ∨
       ((∀ b, u b = true → present st df.ino b = true → r b = true) ∧
          st' = st.setProc { st.proc with dfds := <[fd := { df with rd := .done }]> st.proc.dfds } ∧
          e' = Val (PairV (#([] : GoString)) (PairV (#(1 : w64)) (#(0 : w64))))) ∨
       (∃ e : w64, e ≠ 0 ∧
          st' = st.setProc { st.proc with dfds := <[fd := { df with
            rd := .reading u s r }]> st.proc.dfds } ∧
          e' = Val (PairV (#([] : GoString)) (PairV (#(0 : w64)) (#e)))))
  /- `lstat(p)`'s "is it a directory", as `os.Rename` asks it of its destination:
  `#p ↦ (#isDir, #errno)`. `#1` only for a directory, with a nonzero errno, the one `os.Rename`
  returns then; `#0` otherwise, and for a directory too (the `lstat` failed: `Rename`'s model then
  goes on to `rename(2)`, as Go does). -/
  | "LstatDir" => ∃ (p : GoString) (isDir e : w64), v = #p ∧ st.TreePath p ∧ st' = st ∧
      ((∃ j, st.lookup p = some (.dir j)) ∧ isDir = 1 ∧ e ≠ 0 ∨ isDir = 0) ∧
      e' = Val (PairV (#isDir) (#e))
  /- `rename(2)` of a metadata call (`tok`, from `MetaBegin`): `(tok, #s, #t) ↦ #errno`. As
  `RenameOk` says, or a no-op on an entry renamed to itself; any case may fail, a failure with or
  without the effect. Open fds of a moved file or directory keep it (they hold its inode). -/
  | "Rename" => ∃ (s t : GoString) (k start : Nat), v = PairV (osTokV k) (PairV (#s) (#t)) ∧
      st.TreeName s ∧ st.TreeName t ∧ st.proc.metaCalls !! k = some start ∧
      let st0 := st.metaEnd k
      ((RenameOk st s t ∧ ∃ o, RenameOp st s t o ∧
          (st' = st0.metaDo o start ∧ e' = Val (#(0 : w64)) ∨
           ∃ e : w64, e ≠ 0 ∧ e' = Val (#e) ∧ (st' = st0 ∨ st' = st0.metaDo o start))) ∨
       (s = t ∧ st.lookup s ≠ none ∧ st' = st0 ∧ e' = Val (#(0 : w64))) ∨
       (∃ e : w64, e ≠ 0 ∧ e' = Val (#e) ∧ st' = st0))
  /- `unlink(2)` of a metadata call: `(tok, #p) ↦ #errno`. A file's name is removed (its fds keep
  the file, which stays in `files`); any case may fail, a failure with or without the effect. -/
  | "Unlink" => ∃ (p : GoString) (k start : Nat), v = PairV (osTokV k) (#p) ∧ st.TreeName p ∧
      st.proc.metaCalls !! k = some start ∧
      let st0 := st.metaEnd k
      ((∃ i j b, st.lookup p = some (.file i) ∧ st.parent p = some (j, b) ∧
          (st' = st0.metaDo (.remove j b (.file i)) start ∧ e' = Val (#(0 : w64)) ∨
           ∃ e : w64, e ≠ 0 ∧ e' = Val (#e) ∧
            (st' = st0 ∨ st' = st0.metaDo (.remove j b (.file i)) start))) ∨
       (∃ e : w64, e ≠ 0 ∧ e' = Val (#e) ∧ st' = st0))
  /- `rmdir(2)` of a metadata call: `(tok, #p) ↦ #errno`. An empty directory is removed (an fd on it
  keeps it, empty); any case may fail, a failure with or without the effect. -/
  | "Rmdir" => ∃ (p : GoString) (k start : Nat), v = PairV (osTokV k) (#p) ∧ st.TreeName p ∧
      st.proc.metaCalls !! k = some start ∧
      let st0 := st.metaEnd k
      ((∃ j' j b, EmptyDir st p j' ∧ st.parent p = some (j, b) ∧
          (st' = st0.metaDo (.remove j b (.dir j')) start ∧ e' = Val (#(0 : w64)) ∨
           ∃ e : w64, e ≠ 0 ∧ e' = Val (#e) ∧
            (st' = st0 ∨ st' = st0.metaDo (.remove j b (.dir j')) start))) ∨
       (∃ e : w64, e ≠ 0 ∧ e' = Val (#e) ∧ st' = st0))
  /- `mkdir(2)` of a metadata call: `(tok, #p) ↦ #errno`. A new directory of a fresh inode where
  nothing is, in an existing directory; any case may fail, a failure with or without the effect. -/
  | "Mkdir" => ∃ (p : GoString) (k start : Nat), v = PairV (osTokV k) (#p) ∧ st.TreeName p ∧
      st.proc.metaCalls !! k = some start ∧
      let st0 := st.metaEnd k
      let o (j : Ino) (b : GoString) := MetaOp.mkdir j b st.fs.nextIno
      ((∃ j b, st.lookup p = none ∧ st.parent p = some (j, b) ∧
          (st' = st0.takeIno.metaDo (o j b) start ∧ e' = Val (#(0 : w64)) ∨
           ∃ e : w64, e ≠ 0 ∧ e' = Val (#e) ∧
            (st' = st0 ∨ st' = st0.takeIno.metaDo (o j b) start))) ∨
       (∃ e : w64, e ≠ 0 ∧ e' = Val (#e) ∧ st' = st0))
  /- The first step of `fallocate(fd, 0, off, len)`: `(#fd, #off, #len) ↦ token`, a resize to
  `max size (off + len)` in flight (its visible effect is `ftruncate`'s to that size: zeros past the
  end; the blocks it allocates are not modelled). As `FtruncateStart`: no other change may be in
  flight on the file. Stuck on a negative offset or a length not above 0. -/
  | "FallocStart" => ∃ (fd off len : w64) (t : Nat) (d : OsFd),
      v = PairV (#fd) (PairV (#off) (#len)) ∧ FdOpen st fd d ∧ d.writable ∧ 0 ≤ off.toInt ∧
      0 < len.toInt ∧ ¬ BusyAt st d.ino ∧ st.proc.inflight !! t = none ∧
      st.proc.metaCalls !! t = none ∧
      st' = st.addInflight t ⟨d.ino, .truncate (max (st.size d.ino) (off.toNat + len.toNat))⟩ ∧
      e' = Val (osTokV t)
  /- The second step: `token ↦ #errno`. On failure the file may have grown to any size between its
  size and the target, zero-filled (ext4 grows it as each chunk is allocated). -/
  | "FallocFinish" => ∃ (t : Nat) (i : Ino) (sz : Nat) (f : OsFile), v = osTokV t ∧
      st.proc.inflight !! t = some ⟨i, .truncate sz⟩ ∧ st.file i = some f ∧
      (let st0 := st.doneInflight t
       st' = st0.setFile i (f.truncate sz) ∧ e' = Val (#(0 : w64)) ∨
       ∃ e : w64, e ≠ 0 ∧ e' = Val (#e) ∧
         (st' = st0 ∨ ∃ sz', f.size ≤ sz' ∧ sz' ≤ sz ∧ st' = st0.setFile i (f.truncate sz')))
  /- `fallocate(fd, FALLOC_FL_KEEP_SIZE, off, len)`: `(#fd, #off, #len) ↦ #errno`. No visible change
  (it allocates blocks, which are not modelled); any errno. Stuck on a negative offset or a length
  not above 0. -/
  | "FallocKeep" => ∃ (fd off len e : w64) (d : OsFd), v = PairV (#fd) (PairV (#off) (#len)) ∧
      FdOpen st fd d ∧ d.writable ∧ 0 ≤ off.toInt ∧ 0 < len.toInt ∧ st' = st ∧ e' = Val (#e)
  /- `fcntl(fd, F_OFD_SETLK[W], ...)`: `(#fd, #cmd) ↦ #errno`. Trivial, as `Flock`: the lock state
  is not modelled, so the errno is anything. -/
  | "OfdLock" => ∃ (fd cmd e : w64) (d : OsFd), v = PairV (#fd) (#cmd) ∧ FdOpen st fd d ∧
      st' = st ∧ e' = Val (#e)
  | _ => False

/-- The cells a new mapping takes are free, in `(0, maxAddr]`. -/
def MapsFresh (st st' : OsState) (h : GMap Loc (NonAtomic val)) : Prop :=
  ∀ base m, st'.proc.maps !! base = some m → st.proc.maps !! base = none →
    base.addr + m.len ≤ maxAddr ∧ ∀ k < m.len, h !! (base +ₗ (k : Int)) = none

/-- The step relation: an operation's step, the heap rendered from the new state. -/
def FsStep (op : String) (v : val) (h : GMap Loc (NonAtomic val)) (st : OsState) (_g : Unit)
    (e' : Expr) (h' : GMap Loc (NonAtomic val)) (st' : OsState) (_g' : Unit) : Prop :=
  IsFsStep op v st e' st' ∧ MapsFresh st st' h ∧ HeapRendered st st' h h'

end step

/-! ## Crash -/

/-- `v` is a version a crash may leave in sector `n` of the file `f` of inode `i`: one it had since
its last successful sync (the page cache's included), or the page cache's with each change in flight
on the file landed as some prefix. -/
def SecCand (st : OsState) (i : Ino) (f : OsFile) (n : Nat) (v : SecBytes) : Prop :=
  v ∈ (f.secs n).vers ∨
  ∃ ks f', ks.Perm (changesOn st i) ∧ Landed ks f f' ∧ v = (f'.secs n).last

/-- `f'` is what a machine crash may leave of the file `f` of inode `i`: a size it had since its
last successful sync, or between such a size and one an in-flight change would give it; each sector a
version `SecCand` allows, whole (its bytes past the size included, F3); all of it on disk. -/
def CrashFile (st : OsState) (i : Ino) (f f' : OsFile) : Prop :=
  ∃ (sz : Nat) (vs : Nat → SecBytes),
    ((f.sizeLo ≤ sz ∨ ∃ t c, st.proc.inflight !! t = some c ∧ c.ino = i ∧ c.target st ≤ sz) ∧
     (sz ≤ f.sizeHi ∨ ∃ t c, st.proc.inflight !! t = some c ∧ c.ino = i ∧ sz ≤ c.target st)) ∧
    (∀ n, SecCand st i f n (vs n)) ∧ f' = OsFile.ofDisk vs sz

/-- The file `i` is named in the tree `m`. -/
def Named (m : Tree) (i : Ino) : Prop := ∃ j b, m.entry j b = some (.file i)

/-- A machine crash: the roots stay; the tree is the durable one with a set of the logged operations
replayed in log order, a set that holds the committed ones and is closed under `Follows` (what the
journal may have on disk), all of it durable; every file it names is what a crash may leave of its
file (`CrashFile`); every other file is gone; the process has nothing open or in flight. -/
def MachineCrash (st st' : OsState) : Prop :=
  st'.proc = ProcState.empty ∧ st'.fs.roots = st.fs.roots ∧ st'.fs.metaLog = [] ∧
  (∀ y, ¬ st'.fs.committed y) ∧ st'.fs.nextIno = st.fs.nextIno ∧
  (∃ S : Nat → Prop, (∀ x, S x → x < st.fs.metaLog.length) ∧ (∀ y, st.fs.committed y → S y) ∧
    Closed st.fs.metaLog S ∧ st'.fs.treeDur = replay (keptOps st.fs.metaLog S) st.fs.treeDur) ∧
  ∀ i, (Named st'.fs.treeDur i →
      ∃ f f', st.fs.files !! i = some f ∧ CrashFile st i f f' ∧ st'.fs.files !! i = some f') ∧
    (¬ Named st'.fs.treeDur i → st'.fs.files !! i = none)

/-- A restart of the process alone: the machine's state stays, each change in flight landed as some
prefix (a killed process's system call has done part of its work); a metadata call that had not
taken its step did nothing; the process has nothing open or in flight. Dirty sectors stay dirty: the page cache outlives the process. -/
def ProcRestart (st st' : OsState) : Prop :=
  st'.proc = ProcState.empty ∧ st'.fs.roots = st.fs.roots ∧
  st'.fs.treeDur = st.fs.treeDur ∧ st'.fs.metaLog = st.fs.metaLog ∧
  st'.fs.committed = st.fs.committed ∧ st'.fs.nextIno = st.fs.nextIno ∧
  ∀ i, match st.fs.files !! i with
    | none => st'.fs.files !! i = none
    | some f => ∃ ks f', ks.Perm (changesOn st i) ∧ Landed ks f f' ∧ st'.fs.files !! i = some f'

/-- A crash: of the machine, or of the process alone. -/
def OsCrash (st st' : OsState) : Prop := MachineCrash st st' ∨ ProcRestart st st'

/-- A state a program may start in: the process has nothing open; nothing logged or committed; the
roots and the tree well formed; every inode the tree names is a file, every file named (no orphan
at boot) and all of it on disk (the environment's "durable at first start"); every inode in use
below `nextIno`. -/
def FsInit (st : OsState) : Prop :=
  st.proc = ProcState.empty ∧ st.fs.metaLog = [] ∧ (∀ y, ¬ st.fs.committed y) ∧
  RootsOk st.fs.roots ∧ TreeWf st.fs.roots st.fs.treeDur ∧
  (∀ i, Named st.fs.treeDur i → st.fs.files !! i ≠ none) ∧
  (∀ i f, st.fs.files !! i = some f → Named st.fs.treeDur i ∧ ∃ vs sz, f = OsFile.ofDisk vs sz) ∧
  (∀ i, i ∈ st.fs.files → i < st.fs.nextIno) ∧ (∀ j, j ∈ st.fs.treeDur → j < st.fs.nextIno)

instance fs_semantics : ExtSemantics fsExt where
  step := FsStep
  crash := OsCrash

end Fs
end Perennial

end
