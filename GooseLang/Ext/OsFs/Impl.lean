/-
The Linux file extension of GooseLang [Trusted definitions!].

A node's regular files as Linux exposes them to one process through `pread`, `pwrite`,
`fstat`, `ftruncate`, `fdatasync`/`fsync`, `close` and a read-only shared `mmap`: the page
cache that reads and the mappings see, the image on disk that a crash keeps, and the fds and
mappings of the process. Its Go side is the wrapper package named by `osFsExt.name`, whose
functions mirror the `os`/`syscall`/`golang.org/x/sys/unix` calls bbolt makes; their trusted
models (`TrustedCode/...`) call the operations below and marshal Go values. The design and its
decisions (D1–D8) are in `notes/osfs-ext-plan.md`.

**Environment** (hypotheses of the adequacy statement, not of this file): the paths in the
domain of `files` name distinct regular files on a local ext4 or xfs filesystem; no other
process touches them; the device honours cache flushes, writes each sector atomically and has no
media errors (a torn sector would garble durable neighbours of a dirty byte, and a read error on
a mapped page is SIGBUS where the model's load succeeds). Opening any other path is stuck, so
path resolution is never modelled.

**Soundness discipline.** The model is never more defined than Linux:
* *Misuse is stuck* (D6): a closed, forged or wrong-mode fd, an unsupported flag, `PROT_WRITE`,
  a nonzero `mmap` offset, a `munmap` of anything but a whole mapping, a negative offset.
* *Environmental failure is a nondeterministic errno*: every operation that makes a system call
  may fail with any nonzero errno. On failure, `Open`, `ftruncate` and `Munmap` may or may not
  have had their effect; a failed `pread` read a prefix; a failed `pwrite` wrote a prefix (as
  `generic_perform_write` does, and Go's loop reports); a failed `fsync` loses the
  writeback of the dirty bytes, which later syncs do not redo (D2).
* *Races*: a change to a file's bytes or size (`pwrite`, `ftruncate`) is two steps
  (`PWriteStart`/`PWriteFinish`, `FtruncateStart`/`FtruncateFinish`), and between them any
  mapped load that could see part of it is stuck (a hole), so a real overlap in time is a stuck
  model interleaving, while a racing `pread` or `fstat` returns any mix (`ReadSees`, `StatSees`). A write of `n` bytes at `off` *affects* `[min off size, off + n)`,
  including the zero gap an extending write creates; a truncate affects every byte from
  `min size sz` on, and excludes every other change to the file (`Affects`).
* *Read-only mappings*: a mapped cell is a byte cell born with a phantom reader
  (`Reading 1`), so every store to it is stuck and loads are allowed; a cell past EOF or
  affected by an in-flight change holds a *hole* (`#()`, not a byte), so loads are stuck too
  (SIGBUS, or a race). (Perennial's `CmpXchgBytesFailS` still accepts readers: a failing CAS
  on a mapped word is defined in the model and faults on Linux. See the plan, "Perennial
  prerequisite".)

**Heap.** The operations never touch user memory: the models pass buffers as Go strings. The
one heap rule is `HeapRendered`, applied by every step: the cells of every mapping after the
step show the file (`cellVal`), the cells of a removed mapping are gone, and every other cell is
unchanged.

**Crash** (`OsCrash`): fds, in-flight changes and mappings are gone (the heap is arbitrary
anyway); each file becomes a crash image (`CrashImage`): a file created since boot may vanish
(D4); the size is one the file had since its last successful sync, or that an in-flight change
would give it; a byte is the durable one unless it is dirty, lost by a failed sync, in-flight, or
past the durable image, when it is arbitrary (D1).
-/
module

public import Perennial.GooseLang.Lang

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

/-- The files, fds, in-flight changes and mappings of a node. -/
structure OsState where
  /-- The allowed paths (the domain), and their files (`none`: no such file). -/
  files : GMap GoString (Option OsFile)
  fds : GMap w64 OsFd
  /-- In-flight changes, by the token their first step returned. -/
  inflight : GMap w64 OsChange
  /-- Mappings, by base address. -/
  maps : GMap Loc OsMap

instance : Inhabited OsState := ⟨⟨∅, ∅, ∅, ∅⟩⟩

/-- The Linux file extension. It has no values of its own and no global state. -/
@[reducible] def osFsExt : GooseExt where
  name := "github.com/mit-pdos/etcd-grove/osfs"
  Val := Empty
  LocalState := OsState
  GlobalState := Unit

/-! ## Constants (linux/amd64) -/

def O_RDONLY : Nat := 0x0
def O_WRONLY : Nat := 0x1
def O_RDWR : Nat := 0x2
def O_CREAT : Nat := 0x40
def O_TRUNC : Nat := 0x200
def O_CLOEXEC : Nat := 0x80000
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

/-- The size the change `c` gives its file (a write that extends it, or a truncate). -/
def OsChange.target (c : OsChange) : Nat :=
  match c.kind with
  | .write off data => off + data.length
  | .truncate sz => sz

/-- Some in-flight change may change byte `i` of the file at `p`. -/
def InflightAt (p : GoString) (i : Nat) : Prop :=
  ∃ t c, st.inflight !! t = some c ∧ c.path = p ∧ Affects st c i

/-- Some in-flight change may change the size of the file at `p`: a write that extends it
(its size grows page by page), or any truncate. -/
def ResizingAt (p : GoString) : Prop :=
  ∃ t c, st.inflight !! t = some c ∧ c.path = p ∧
    match c.kind with
    | .write _ _ => st.size p < c.target
    | .truncate _ => True

/-- Some change is in flight on the file at `p`. -/
def BusyAt (p : GoString) : Prop := ∃ t c, st.inflight !! t = some c ∧ c.path = p

/-- What a `pread` of `n` bytes at `off` of the file at `p` may return: at most `n` bytes; exactly
the bytes up to EOF unless a change is resizing the file; and each byte the file's, unless an
in-flight change may change it, when it is arbitrary (Linux returns some mix). -/
def ReadSees (p : GoString) (off n : Nat) (r : List w8) : Prop :=
  r.length ≤ n ∧ (¬ ResizingAt st p → r.length = min n (st.size p - off)) ∧
  ∀ i (h : i < r.length), ¬ InflightAt st p (off + i) →
    ((st.file p).map (·.cur)).bind (·[off + i]?) = some r[i]

/-- What `fstat` may give as the size of the file at `p`: its size, or, while a change resizes it,
a size between its size and the change's target (an extending write grows it page by page). -/
def StatSees (p : GoString) (sz : Nat) : Prop :=
  sz = st.size p ∨ ∃ t c, st.inflight !! t = some c ∧ c.path = p ∧
    min (st.size p) c.target ≤ sz ∧ sz ≤ max (st.size p) c.target

/-- `l` is byte `i` of a mapping of the file at `p`. Mappings are disjoint: each lies in cells
that were free when it was made. -/
def MapsTo (l : Loc) (p : GoString) (i : Nat) : Prop :=
  ∃ base m, st.maps !! base = some m ∧ m.path = p ∧ i < m.len ∧ l = base +ₗ (i : Int)

/-- `l` is a cell of some mapping. -/
def Mapped (l : Loc) : Prop := ∃ p i, MapsTo st l p i

open Classical in
/-- What byte `i` of a mapping of `p` holds: the file's byte, or a hole (`#()`) past EOF or
where an in-flight change may be changing it. -/
noncomputable def cellVal [GooseExts] [GoGlobalContext] (p : GoString) (i : Nat) : val :=
  match st.file p with
  | some f => if h : i < f.cur.length then
      (if InflightAt st p i then #() else LitV (LitByte f.cur[i])) else #()
  | none => #()

end derived

/-- The heap after a step from `st` to `st'`: every mapping of `st'` shows its file (a cell
that was already mapped keeps its mode; a new one is born with a phantom reader, so no store
succeeds); a cell mapped in `st` only is gone; every other cell is unchanged. -/
def HeapRendered [GooseExts] [GoGlobalContext] (st st' : OsState) (h h' : GMap Loc (NonAtomic val)) : Prop :=
  (∀ l p i, MapsTo st' l p i → Mapped st l →
    ∃ m v0, h !! l = some (m, v0) ∧ h' !! l = some (m, cellVal st' p i)) ∧
  (∀ l p i, MapsTo st' l p i → ¬ Mapped st l → h' !! l = some (Reading 1, cellVal st' p i)) ∧
  (∀ l, ¬ Mapped st' l → Mapped st l → h' !! l = none) ∧
  (∀ l, ¬ Mapped st' l → ¬ Mapped st l → h' !! l = h !! l)

/-! ## Effects -/

section effects

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

end effects

/-! ## The step relation -/

section step
variable [GooseExts] [GoGlobalContext]

/-- A result and an errno, as the Go wrapper's models take them apart. -/
abbrev osRes (v : val) (e : w64) : Expr := Val (PairV v (#e))

/-- An open fd and its description. -/
def FdOpen (st : OsState) (fd : w64) (d : OsFd) : Prop := st.fds !! fd = some d

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
          st.fds !! fd = none ∧
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
  /- The first step of `pwrite(fd, data, off)`: `(#fd, #off, #data) ↦ #token`. It makes no
  system call and cannot fail. The bytes it may change must be clear of every other change. -/
  | "PWriteStart" => ∃ (fd off : w64) (data : List w8) (d : OsFd) (t : w64),
      v = PairV (#fd) (PairV (#off) (#data)) ∧ FdOpen st fd d ∧ d.writable ∧ 0 ≤ off.toInt ∧
      (let c : OsChange := ⟨d.path, .write off.toNat data⟩
       (∀ i, Affects st c i → ¬ InflightAt st d.path i) ∧
       st.inflight !! t = none ∧ st' = { st with inflight := <[t := c]> st.inflight }) ∧
      e' = Val (#t)
  /- The second step: `#token ↦ (#written, #errno)`. A prefix of the data is written: all of
  it and errno 0, or any prefix and a nonzero errno. -/
  | "PWriteFinish" => ∃ (t : w64) (p : GoString) (off : Nat) (data : List w8) (f : OsFile)
      (k : Nat) (e : w64), v = #t ∧ st.inflight !! t = some ⟨p, .write off data⟩ ∧
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
  /- The first step of `ftruncate(fd, sz)`: `(#fd, #sz) ↦ #token`. It makes no system call
  and cannot fail. No other change may be in flight on the file. -/
  | "FtruncateStart" => ∃ (fd sz t : w64) (d : OsFd), v = PairV (#fd) (#sz) ∧ FdOpen st fd d ∧
      d.writable ∧ 0 ≤ sz.toInt ∧ ¬ BusyAt st d.path ∧ st.inflight !! t = none ∧
      st' = { st with inflight := <[t := ⟨d.path, .truncate sz.toNat⟩]> st.inflight } ∧
      e' = Val (#t)
  /- The second step: `#token ↦ #errno`. On failure the file may or may not be resized. -/
  | "FtruncateFinish" => ∃ (t : w64) (p : GoString) (sz : Nat) (f : OsFile), v = #t ∧
      st.inflight !! t = some ⟨p, .truncate sz⟩ ∧ st.file p = some f ∧
      (let st0 := { st with inflight := GMap.delete t st.inflight }
       let st1 := st0.setFile p (f.truncate sz)
       st' = st1 ∧ e' = Val (#(0 : w64)) ∨
       ∃ e : w64, e ≠ 0 ∧ e' = Val (#e) ∧ (st' = st0 ∨ st' = st1))
  /- `fsync(fd)` and `fdatasync(fd)` alike (D3): `#fd ↦ #errno`. -/
  | "Fsync" => ∃ (fd : w64) (d : OsFd) (f : OsFile), v = #fd ∧ FdOpen st fd d ∧ st.file d.path = some f ∧
      (st' = st.setFile d.path (f.synced (InflightAt st d.path ·)) ∧ e' = Val (#(0 : w64)) ∨
       ∃ e : w64, e ≠ 0 ∧ e' = Val (#e) ∧
         st' = st.setFile d.path (f.syncFailed (InflightAt st d.path ·)))
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
      ∃ t c, st.inflight !! t = some c ∧ c.path = p ∧ c.target ≤ img.length) ∧
     (img.length ≤ f.sizeHi ∨
      ∃ t c, st.inflight !! t = some c ∧ c.path = p ∧ img.length ≤ c.target)) ∧
  ∀ i (hi : i < img.length), ¬ f.dirty i → ¬ f.lost i → ¬ InflightAt st p i →
    (hd : i < f.durable.length) → img[i] = f.durable[i]

/-- A crash: fds, in-flight changes and mappings are gone; each file becomes a crash image, as
on disk at the next boot, or vanishes if it was created since boot. -/
def OsCrash (st st' : OsState) : Prop :=
  st'.fds = ∅ ∧ st'.inflight = ∅ ∧ st'.maps = ∅ ∧
  ∀ p, match st.files !! p with
    | none => st'.files !! p = none
    | some none => st'.files !! p = some none
    | some (some f) => (¬ f.named ∧ st'.files !! p = some none) ∨
        ∃ img, CrashImage st p f img ∧ st'.files !! p = some (some (OsFile.ofDisk img))

instance osFs_semantics : ExtSemantics osFsExt where
  step := OsStep
  crash := OsCrash

end Perennial
