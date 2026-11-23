/-
Crash-aware specs of `os` (this repository's, project `bboltfs`): the shared definitions.

A crash proof takes the old generation's files after a crash from what an invariant holds
(`GooseLang/Ext/Fs/CrashTok.lean`'s `osCrash_take_runs_keep`), and what the crash left at a path
from the claims an invariant holds (`crashRest_region'`), so a file's ghost resources (`osMeta`,
`osBytes`) and the claim on its name must be in an invariant at every step, including the steps
inside an `os` call. The crash-aware specs (`Spec/os/Crash.lean`) cover a file `p` directly under a
root (`FileAt R p j b`: `p` is the name `b` of the root directory `j`). They keep the file and half
of the claim on `b` (`osNames j (.only [b])`) in an invariant `cfInv N p R γ Good` and open it
around each of the extension's steps:

* The file's state is `CFile`: no file at `p` (`none`), idle (`some (i, m, bs, none)`: its inode,
  `OsMeta` `m` and all its bytes `bs`), or with a `pwrite` in flight (`some (i, m, bs, some (t, off,
  data, n))`: the token `t` holds `m` and the bytes it changes).
* The invariant holds a ghost variable `γ` naming the state, half of the file's resources (all of
  what a change in flight holds, its token), half of the claim (its history `h`), and
  `CrashOk Good j b s h`: every crash of the claim, whatever entries it keeps (`NamesH.valAfter`,
  what `RegionCrashed` concludes), leaves `b` naming nothing (then `Good none`) or the state's file
  (`TreeOk`), and every file a crash may leave of the state is `Good` (`FileOk`: every file the
  ghost state allows, `FileCrashedR`, each byte one of its crash candidates). The caller holds
  the other halves (`cfOwn`), so it knows the state and the claim exactly.
* A crash-aware spec moves the state; the caller shows `FileOk Good` of the states the call passes
  through (the claim's part is the spec's: only a create changes it).
* After a crash, `cfInv_crash_keep` takes the file from the invariant's half and, from the claim's
  half (`crashRest_region'`), what the new tree names at `p`: none, or the file, `Good`.
* A generation starts the invariant from the claim on `b` its start resources hold
  (`osShared_file`, `cfInv_alloc`).

`Good` is a predicate of what a crash leaves at `p`, so the specs are the same for any crash
invariant of a single file; mappings are not covered (`CfWf` asks for none).
-/
module

public import Proof.os.Base
public import GooseLang.Ext.Fs.CrashTok
public import GooseLang.Ext.Fs.TreeShared
public import GooseLang.Ext.Fs.Specs


@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

/-! ## The extension's operations are atomic -/

section atomic
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]

/-- Every step of an operation of the extension but `mmap` and the lock calls ends in a value (`mmap`
may step to itself, `MmapStall`; a blocking lock request waits, `LockStep`). -/
theorem fsStep_val {o : String} {v : val} {h : GMap Loc (NonAtomic val)} {st : OsState}
    {e' : Expr} {h' : GMap Loc (NonAtomic val)} {st' : OsState} (hM : o ≠ "Mmap")
    (hF : o ≠ "Flock") (hO : o ≠ "OfdLock")
    (hs : FsStep o v h st () e' h' st' ()) : (toVal e').isSome := by
  obtain ⟨hs, -, -⟩ := fsStepV_of_ne hM hs
  unfold IsFsStep at hs
  split at hs <;> (try simp only at hs) <;>
  repeat' (first
    | exact absurd rfl hF
    | exact absurd rfl hO
    | exact hs.elim
    | (subst hs; rfl)
    | (refine Or.elim hs (fun hs => ?_) (fun hs => ?_))
    | (refine And.elim (fun hl hs => ?_) hs; first | (subst hl; rfl) | skip)
    | (refine Exists.elim hs (fun _ hs => ?_)))

/-- The operations of the extension that always return: all but `mmap`, which may step to itself
(`MmapStall`), and the lock calls (`Flock`, `OfdLock`), whose blocking requests may wait (`LockStep`).
An instance for each, so that `fsOp_atomic` is found for the literal operation. -/
class FsRetOp (o : String) : Prop where
  ne_mmap : o ≠ "Mmap"
  ne_flock : o ≠ "Flock"
  ne_ofd : o ≠ "OfdLock"

instance : FsRetOp "Open" := ⟨by decide, by decide, by decide⟩
instance : FsRetOp "PRead" := ⟨by decide, by decide, by decide⟩
instance : FsRetOp "PWriteStart" := ⟨by decide, by decide, by decide⟩
instance : FsRetOp "PWriteFinish" := ⟨by decide, by decide, by decide⟩
instance : FsRetOp "Fstat" := ⟨by decide, by decide, by decide⟩
instance : FsRetOp "FtruncateStart" := ⟨by decide, by decide, by decide⟩
instance : FsRetOp "FtruncateFinish" := ⟨by decide, by decide, by decide⟩
instance : FsRetOp "Fsync" := ⟨by decide, by decide, by decide⟩
instance : FsRetOp "Close" := ⟨by decide, by decide, by decide⟩
instance : FsRetOp "Munmap" := ⟨by decide, by decide, by decide⟩
instance : FsRetOp "FdKind" := ⟨by decide, by decide, by decide⟩
instance : FsRetOp "OutSync" := ⟨by decide, by decide, by decide⟩
instance : FsRetOp "OutClose" := ⟨by decide, by decide, by decide⟩
instance : FsRetOp "PathKind" := ⟨by decide, by decide, by decide⟩
instance : FsRetOp "CallBegin" := ⟨by decide, by decide, by decide⟩
instance : FsRetOp "DirSync" := ⟨by decide, by decide, by decide⟩
instance : FsRetOp "DirClose" := ⟨by decide, by decide, by decide⟩
instance : FsRetOp "DirReadNext" := ⟨by decide, by decide, by decide⟩
instance : FsRetOp "LstatDir" := ⟨by decide, by decide, by decide⟩
instance : FsRetOp "Rename" := ⟨by decide, by decide, by decide⟩
instance : FsRetOp "Unlink" := ⟨by decide, by decide, by decide⟩
instance : FsRetOp "Rmdir" := ⟨by decide, by decide, by decide⟩
instance : FsRetOp "Mkdir" := ⟨by decide, by decide, by decide⟩
instance : FsRetOp "FallocStart" := ⟨by decide, by decide, by decide⟩
instance : FsRetOp "FallocFinish" := ⟨by decide, by decide, by decide⟩
instance : FsRetOp "FallocKeep" := ⟨by decide, by decide, by decide⟩
instance : FsRetOp "Madvise" := ⟨by decide, by decide, by decide⟩

/-- An operation of the extension other than `mmap` is atomic: it takes one step, to a value. -/
instance fsOp_atomic (a : Language.Atomicity) (o : String) [ho : FsRetOp o] (v : val) :
    Language.Atomic a (ExternalOp fsExt.name o (Val v)) :=
  goose_atomic a (fun _ _ e' _ _ hb => by
      cases hb with
      | ExternalOpS _ _ _ _ _ _ hst =>
        obtain ⟨_, _, _, hst', rfl⟩ := (extStep_named _ _ _ _ _).1 hst
        exact fsStep_val ho.ne_mmap ho.ne_flock ho.ne_ofd
          (FsSemOk.step_sub _ _ _ _ _ _ _ _ _ ((HasExt.step_iff ..).1 hst')))
    (by intro Ki e' h; cases Ki <;> simp only [fillItem] at h <;> cases h <;> rfl)

end atomic

/-! ## The file's state and what a crash leaves of it -/

/-- What the crash-aware specs track of an existing file: its `OsMeta`, all its bytes, and a
`pwrite` in flight if any (its token, offset, data and number). -/
abbrev CX := OsMeta × List ByteG × Option (Nat × Nat × List w8 × Nat)

/-- A file as the crash-aware specs track it: none at the path (`none`); its inode, `OsMeta` and
all its bytes (`some (i, m, bs, none)`); or with a `pwrite` of `data` at `off` in flight, the
change number `n`, whose token `t` holds `m` and the bytes it changes
(`some (i, m, bs, some (t, off, data, n))`, `bs` the bytes before it). -/
abbrev CFile := Option (Ino × CX)

/-- The inode of the state's file. -/
def cIno : CFile → Option Ino
  | none => none
  | some (i, _) => some i

/-- The first byte a write at `off` takes of a file of size `m.size`. -/
def cfLo (m : OsMeta) (off : Nat) : Nat := min off m.size

/-- The end of the bytes a write of `n` bytes at `off` takes of a file of size `m.size`. -/
def cfHi (m : OsMeta) (off n : Nat) : Nat := min (off + n) m.size

/-- The bytes such a write takes. -/
def cfRange (m : OsMeta) (bs : List ByteG) (off n : Nat) : List ByteG :=
  (bs.drop (cfLo m off)).take (cfHi m off n - cfLo m off)

/-- The `OsMeta` a write of `n` bytes at `off` holds while in flight: as its first step announced
it (`TokInfo.meta` of its token). -/
def cfMeta (m : OsMeta) (off n : Nat) : OsMeta :=
  m.announce (min off m.size) (off + n) (max m.size (off + n))

/-- What the old generation knows of an existing file for a crash, without its inode: its
`OsMeta` (as a write in flight announced it)... -/
def fMeta : CX → OsMeta
  | (m, _, none) => m
  | (m, _, some (_, off, data, _)) => cfMeta m off data.length

/-- ... and the runs of bytes it holds (with a write in flight, the bytes its token holds, their
candidates with the write's announced, and the caller's halves around them). -/
def fRuns : CX → List (Nat × DFrac × List ByteG)
  | (_, bs, none) => [(0, DFrac.own (1 : Qp).half, bs)]
  | (m, bs, some (_, off, data, n)) =>
      [(cfLo m off, DFrac.own 1, pwAnn data n (cfRange m bs off data.length)),
       (0, DFrac.own (1 : Qp).half, bs.take (cfLo m off)),
       (cfHi m off data.length, DFrac.own (1 : Qp).half, bs.drop (cfHi m off data.length))]

/-- Every file a crash may leave of an existing file `x` is `Good`: every file of a size within
its `OsMeta`'s bounds, on disk, each byte of its runs one of its crash candidates (and zeros past
the zeros known, `FileCrashedR`). Not of its inode. -/
def FileOk (Good : Option OsFile → Prop) (x : CX) : Prop :=
  ∀ f, FileCrashedR (fMeta x) (fRuns x) (some f) → Good (some f)


/-! ## The file's name, and what a crash leaves at it -/

/-- `p` is the name `b` of the root directory `j` (the roots `R` well formed): the files the
crash-aware specs cover. What any tree names at `p` is what it names at `j`'s `b`
(`lookupH_fileAt`). -/
def FileAt (R : Roots) (p : GoString) (j : Ino) (b : GoString) : Prop :=
  RootsOk R ∧ NameOk b ∧ ∃ r, (r, j) ∈ R ∧ p = child r b

/-- `FileAt` names one directory and one name. -/
theorem fileAt_unique {R : Roots} {p : GoString} {j j' : Ino} {b b' : GoString}
    (h : FileAt R p j b) (h' : FileAt R p j' b') : j = j' ∧ b = b' := by
  obtain ⟨hR, hb, r, hr, rfl⟩ := h
  obtain ⟨-, hb', r', hr', he⟩ := h'
  have hbb : b = b' := by
    have := congrArg baseOf he
    rwa [baseOf_child' _ _ hb, baseOf_child' _ _ hb'] at this
  subst hbb
  have hrr : r = r' := by
    have := congrArg parentOf he
    rw [parentOf_child' _ _ hb, parentOf_child' _ _ hb] at this
    exact Option.some.inj this
  subst hrr
  have := eq_of_nodup_map hR.1 hr hr' rfl
  exact ⟨(Prod.mk.inj this).2, rfl⟩

/-- The directory of `d/b`, a file of `FileAt`, is the root `d`. -/
theorem fileAt_root {R : Roots} {d b b' : GoString} {j : Ino} (h : FileAt R (child d b) j b')
    (hb : NameOk b) : (d, j) ∈ R ∧ b' = b := by
  obtain ⟨-, hb', r, hr, he⟩ := h
  have h1 := congrArg baseOf he
  rw [baseOf_child' _ _ hb, baseOf_child' _ _ hb'] at h1
  subst h1
  have h2 := congrArg parentOf he
  rw [parentOf_child' _ _ hb, parentOf_child' _ _ hb] at h2
  cases h2
  exact ⟨hr, rfl⟩

/-- A root names its directory, whatever the history. -/
theorem lookupH_root {R : Roots} (hr : RootsOk R) {d : GoString} {j : Ino} (hd : (d, j) ∈ R)
    (V : Hist) : lookupH R V d = some (.dir j) := by
  have := lookup_joinPath (st := Hist.st R V) hr hd (cs := []) (by simp)
  simp only [joinPath, List.flatMap_nil, List.append_nil, walk] at this
  exact this

/-- What a tree names at `p` is what it names at `j`'s `b`. -/
theorem lookupH_fileAt {R : Roots} {p : GoString} {j : Ino} {b : GoString} (h : FileAt R p j b)
    (V : Hist) : lookupH R V p = V.now.entry j b := by
  obtain ⟨hR, hb, r, hr, rfl⟩ := h
  exact lookup_child (st := Hist.st R V) hR (lookupH_root hR hr V) hb

/-- Every crash of the claim on the name `b` of the directory `j`, of history `h`, whatever
entries it keeps (`NamesH.valAfter`: what `RegionCrashed` concludes of a crash), leaves `b`
naming nothing (and then `Good none`) or the file `io`, if any. -/
def TreeOkI (Good : Option OsFile → Prop) (j : Ino) (b : GoString) (io : Option Ino) (h : NamesH) :
    Prop :=
  ∀ K : Nat → Prop,
    (h.valAfter j K b = none ∧ Good none) ∨ ∃ i, io = some i ∧ h.valAfter j K b = some (.file i)

/-- Every crash of the claim leaves `b` naming nothing (and then `Good none`) or the state's
file. -/
abbrev TreeOk (Good : Option OsFile → Prop) (j : Ino) (b : GoString) (s : CFile) (h : NamesH) :
    Prop :=
  TreeOkI Good j b (cIno s) h

/-- What a crash may leave of the state `s` and the claim `h` on `j`'s `b` is `Good`. -/
def CrashOk (Good : Option OsFile → Prop) (j : Ino) (b : GoString) (s : CFile) (h : NamesH) :
    Prop :=
  TreeOk Good j b s h ∧ ∀ i x, s = some (i, x) → FileOk Good x

/-- What specs keep of a state: all of the file's bytes, and no mapping. -/
def CfWf : CFile → Prop
  | none => True
  | some (_, m, bs, _) => bs.length = m.size ∧ m.maps = ∅

/-- The fd `open(O_RDWR|O_CREAT|O_CLOEXEC)` gives: readable and writable. -/
theorem openFd_rw (i : Ino) : openFd i (W64 0x80042) = ⟨i, true, true, none, none⟩ := by
  simp [openFd, O_WRONLY, O_RDONLY]

/-- What `b` names now (the claim's `cur`): nothing, or the state's file. -/
def PathOk (b : GoString) (s : CFile) (h : NamesH) : Prop :=
  match s with
  | none => h.cur !! b = none
  | some (i, _) => h.cur !! b = some (.file i)

/-- An entry not kept leaves what a crash leaves of a name as it was. -/
theorem cf_valAfter_skip (h : NamesH) (j : Ino) (K : Nat → Prop) (b : GoString) (x : Nat)
    (e : LogEntry) (c : Ents) (hn : ¬ K x) :
    (h.log x e c).valAfter j K b = h.valAfter j K b := by
  classical
  unfold NamesH.valAfter NamesH.log
  simp [List.filter_append, hn]

/-- A kept last entry writing a name leaves the name as right after it. -/
theorem cf_valAfter_last (h : NamesH) (j : Ino) (K : Nat → Prop) (b : GoString) (x : Nat)
    (e : LogEntry) (c : Ents) (hK : K x) (hw : e.op.Writes j b) :
    (h.log x e c).valAfter j K b = c !! b := by
  classical
  unfold NamesH.valAfter NamesH.log
  simp [List.filter_append, hK, hw]

/-- **The claim after the create** of the file `i` at `b`, from no file there: every crash leaves
`b` naming nothing, as before the create, or the file. -/
theorem treeOk_create {Good : Option OsFile → Prop} {j : Ino} {b : GoString} {h : NamesH}
    {i : Ino} (x s0 : Nat) (y : CX) (htr : TreeOk Good j b none h) :
    TreeOk Good j b (some (i, y))
      (h.log x ⟨.create j b i, s0⟩ (<[b := .file i]> h.cur)) := by
  intro K
  by_cases hK : K x
  · right
    refine ⟨i, rfl, ?_⟩
    rw [cf_valAfter_last _ _ _ _ _ _ _ hK (.inl (by simp [MetaOp.slots]))]
    exact GMap.lookup_insert _ _ _
  · rw [cf_valAfter_skip _ _ _ _ _ _ _ hK]
    rcases htr K with h1 | ⟨i', hi, -⟩
    · exact .inl h1
    · cases hi

/-- A generation's claim on `b` (nothing logged): every crash leaves `b` as the tree has it. -/
theorem namesOf_nil_valAfter (V : Hist) (hV : V.2 = []) (j : Ino) (b : GoString)
    (K : Nat → Prop) : (namesOf V j (.only [b])).valAfter j K b = V.now.entry j b := by
  obtain ⟨m, l⟩ := V
  simp only at hV
  subst hV
  unfold NamesH.valAfter namesOf
  simp only [List.length_nil, List.range_zero, List.filterMap_nil, List.filter_nil,
    List.getLast?_nil]
  rw [restrictN_lookup _ _ _ (by simp [NameSet.Mem]), entsOf_lookup]
  rfl

/-- What a claim on `b` knows `b` names now. -/
theorem namesOf_cur (V : Hist) (j : Ino) (b : GoString) :
    (namesOf V j (.only [b])).cur !! b = V.now.entry j b := by
  unfold namesOf
  simp only
  rw [restrictN_lookup _ _ _ (by simp [NameSet.Mem]), entsOf_lookup]

/-- A generation's claim on `b`: `TreeOk` of the state `p` names (`PathOk`), if `Good` holds of
no file when there is none. -/
theorem treeOk_init {Good : Option OsFile → Prop} {V : Hist} (hV : V.2 = []) {j : Ino}
    {b : GoString} {s : CFile} (hp : PathOk b s (namesOf V j (.only [b])))
    (hg : V.now.entry j b = none → Good none) : TreeOk Good j b s (namesOf V j (.only [b])) := by
  intro K
  rw [namesOf_nil_valAfter V hV]
  rcases s with _ | ⟨i, x⟩
  · have hn : V.now.entry j b = none := by rw [← namesOf_cur]; exact hp
    exact .inl ⟨hn, hg hn⟩
  · exact .inr ⟨i, rfl, by rw [← namesOf_cur]; exact hp⟩

/-! ## The invariant -/

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- What the invariant holds of the state: half of the `OsMeta` and of the bytes, or, while a
write is in flight, its token and half of the bytes around it. -/
def invRes : CFile → IProp GF
  | none => iprop(emp)
  | some (i, m, bs, none) => iprop(osMeta (L := L) i (DFrac.own (1 : Qp).half) m ∗
      osBytes (L := L) i 0 (DFrac.own (1 : Qp).half) bs)
  | some (i, m, bs, some (t, off, data, n)) => iprop(
      pwTok (L := L) t i off data m (cfRange m bs off data.length) n ∗
      osBytes (L := L) i 0 (DFrac.own (1 : Qp).half) (bs.take (cfLo m off)) ∗
      osBytes (L := L) i (cfHi m off data.length) (DFrac.own (1 : Qp).half)
        (bs.drop (cfHi m off data.length)))

/-- What the caller holds of the state: the other halves. -/
def thrRes : CFile → IProp GF
  | none => iprop(emp)
  | some (i, m, bs, none) => iprop(osMeta (L := L) i (DFrac.own (1 : Qp).half) m ∗
      osBytes (L := L) i 0 (DFrac.own (1 : Qp).half) bs)
  | some (i, m, bs, some (_, off, data, _)) => iprop(
      osBytes (L := L) i 0 (DFrac.own (1 : Qp).half) (bs.take (cfLo m off)) ∗
      osBytes (L := L) i (cfHi m off data.length) (DFrac.own (1 : Qp).half)
        (bs.drop (cfHi m off data.length)))

/-- The invariant of the file at `p` (the name `b` of the root directory `j`): its state `s`
(named by `γ`), the invariant's half of it and of the claim on `b` (of history `h`), and what a
crash may leave of them is `Good`. -/
def cfInv (N : Namespace) (p : GoString) (R : Roots) (γ : GName) (Good : Option OsFile → Prop) :
    IProp GF :=
  inv N iprop(∃ (s : CFile) (j : Ino) (b : GoString) (h : NamesH), ⌜FileAt R p j b⌝ ∗
    ghostVar γ (1 : Qp).half s ∗ invRes (L := L) s ∗
    osNames (L := L) j (.only [b]) (DFrac.own (1 : Qp).half) h ∗ ⌜CrashOk Good j b s h⌝)

instance cfInv_persistent (N : Namespace) (p : GoString) (R : Roots) (γ : GName)
    (Good : Option OsFile → Prop) : Persistent (cfInv (L := L) N p R γ Good) := by
  unfold cfInv; infer_instance

/-- The caller's part of the file at `p` in the state `s`: the other halves, of the state and of
the claim. -/
def cfOwn (p : GoString) (R : Roots) (γ : GName) (s : CFile) : IProp GF :=
  iprop(∃ (j : Ino) (b : GoString) (h : NamesH), ghostVar γ (1 : Qp).half s ∗ thrRes (L := L) s ∗
    osNames (L := L) j (.only [b]) (DFrac.own (1 : Qp).half) h ∗
    ⌜CfWf s ∧ PathOk b s h ∧ FileAt R p j b⌝)

theorem osMeta_halves (i : Ino) (m : OsMeta) :
    osMeta (L := L) i (DFrac.own 1) m ⊣⊢
      osMeta (L := L) i (DFrac.own (1 : Qp).half) m ∗ osMeta (L := L) i (DFrac.own (1 : Qp).half) m := by
  have h := gElem_split (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm i (1 : Qp).half (1 : Qp).half m
  rw [Qp.half_add_half] at h
  exact h

theorem osBytes_halves (i : Ino) (off : Nat) (xs : List ByteG) :
    osBytes (L := L) i off (DFrac.own 1) xs ⊣⊢
      osBytes (L := L) i off (DFrac.own (1 : Qp).half) xs ∗
        osBytes (L := L) i off (DFrac.own (1 : Qp).half) xs := by
  unfold osBytes bytesG
  refine BiEntails.trans ?_ BigSepL.bigSepL_sep_eqv
  constructor
  · apply BigSepL.bigSepL_mono_of_forall; intro k x
    have h := gElem_split (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb (i, off + k)
      (1 : Qp).half (1 : Qp).half x
    rw [Qp.half_add_half] at h
    exact h.1
  · apply BigSepL.bigSepL_mono_of_forall; intro k x
    have h := gElem_split (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb (i, off + k)
      (1 : Qp).half (1 : Qp).half x
    rw [Qp.half_add_half] at h
    exact h.2


/-- The file at `p` as a generation starts with it, as a state: the start's file, on disk. -/
def startState (i : Ino) (f : OsFile) : CFile := some (i, initMeta f, f.contents.map durB, none)

theorem startState_wf (i : Ino) (f : OsFile) : CfWf (startState i f) :=
  ⟨by simp [initMeta, OsFile.contents], rfl⟩

/-- What the generation's start gives of the state `s`: nothing, or its file whole. -/
def startRes : CFile → IProp GF
  | none => iprop(emp)
  | some (i, m, bs, _) => iprop(osMeta (L := L) i (DFrac.own 1) m ∗ osBytes (L := L) i 0 (DFrac.own 1) bs)


theorem osNames_halves' (j : Ino) (N : NameSet) (h : NamesH) :
    osNames (L := L) j N (DFrac.own 1) h ⊣⊢
      osNames (L := L) j N (DFrac.own (1 : Qp).half) h ∗
        osNames (L := L) j N (DFrac.own (1 : Qp).half) h := by
  have h2 := osNames_frac (L := L) j N (1 : Qp).half (1 : Qp).half h
  rw [Qp.half_add_half] at h2
  exact h2

/-- **The file at `p` and the claim on its name, in an invariant**, if a crash of them is
`Good`. -/
theorem cfInv_alloc (N : Namespace) (p : GoString) (R : Roots) (j : Ino) (b : GoString)
    (h : NamesH) (Good : Option OsFile → Prop) (s : CFile)
    (hs : ∀ i m bs x, s ≠ some (i, m, bs, some x)) (hfa : FileAt R p j b)
    (hok : CrashOk Good j b s h) (hwf : CfWf s) (hp : PathOk b s h) :
    ⊢ osNames (L := L) j (.only [b]) (DFrac.own 1) h -∗ startRes (L := L) s ={⊤}=∗ ∃ γ,
      cfInv (L := L) N p R γ Good ∗ cfOwn (L := L) p R γ s := by
  iintro Ht Hf
  imod ghostVar_alloc (GF := GF) s with ⟨%γ, Hv⟩
  icases (ghostVar_split_half (A := CFile) γ 1 _).1 $$ Hv with ⟨Hv1, Hv2⟩
  icases (osNames_halves' j _ h).1 $$ Ht with ⟨Ht1, Ht2⟩
  ihave ⟨Hi, Hth⟩ := (show startRes (L := L) s ⊢ invRes (L := L) s ∗ thrRes (L := L) s by
    rcases s with _ | ⟨i, m, bs, _ | x⟩
    · iintro -; isplitl [] <;> iempintro
    · dsimp only [startRes, invRes, thrRes]
      iintro ⟨Hm, Hb⟩
      icases (osMeta_halves i m).1 $$ Hm with ⟨Hm1, Hm2⟩
      icases (osBytes_halves i 0 bs).1 $$ Hb with ⟨Hb1, Hb2⟩
      iframe
    · exact absurd rfl (hs i m bs x)) $$ Hf
  imod inv_alloc N ⊤ (iprop(∃ (s : CFile) (j : Ino) (b : GoString) (h : NamesH),
      ⌜FileAt R p j b⌝ ∗ ghostVar γ (1 : Qp).half s ∗ invRes (L := L) s ∗
      osNames (L := L) j (.only [b]) (DFrac.own (1 : Qp).half) h ∗ ⌜CrashOk Good j b s h⌝))
      $$ [Hv1 Hi Ht1] with #Hinv
  · inext; iexists s, j, b, h; iframe; isplitr
    · ipureintro; exact hfa
    ipureintro; exact hok
  imodintro
  iexists γ
  unfold cfInv cfOwn
  iframe Hinv
  iexists j, b, h
  iframe Hv2 Hth Ht2
  ipureintro; exact ⟨hwf, hp, hfa⟩

/-- **A generation's claim on a root's name** (and the root's whole call permission), out of its
start resources (`osShared`), the tree well formed: the claim's history is the tree's
(`namesOf`, nothing logged when `V.2 = []`). -/
theorem osShared_file (R : Roots) (V : Hist) (r : GoString) (j : Ino) (b : GoString) (E : CoPset)
    (hE : ↑osShN ⊆ E) (hR : RootsOk R) (hr : (r, j) ∈ R) (hw : TreeWf R V.now) :
    ⊢ osShared (L := L) R V ={E}=∗ osSharedInv (L := L) R ∗ osCallPerm (L := L) (callKey R r) 1 ∗
      osNames (L := L) j (.only [b]) (DFrac.own 1) (namesOf V j (.only [b])) := by
  unfold osShared
  iintro ⟨#Hsi, -, Hperms, -, Hcl⟩
  icases osCallPerms_root R r j hR hr $$ Hperms with ⟨Hp, -⟩
  have hj : j ∈ dirsOf V := by
    have hm : j ∈ V.now := hw.1 j (.root r j hr)
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hm
    exact List.mem_map.2 ⟨(j, v), (GMap.mem_toList _ _ _).2 hv, rfl⟩
  ihave Hj := (BigSepL.bigSepL_mem (Φ := fun j => osNames (L := L) j (.except []) (DFrac.own 1)
    (namesOf V j (.except []))) hj) $$ Hcl
  imod osNames_split R j (.except []) [b] _ hE $$ Hsi Hj with ⟨Hb, -⟩
  have hb : (NameSet.except []).inter [b] = .only [b] := by
    simp [NameSet.inter]
  rw [namesOf_restrict V j (.except []) ((NameSet.except []).inter [b]) (fun c _ => by
    simp [NameSet.Mem]), hb]
  imodintro
  iframe Hsi Hp Hb

end res

/-! ## After a crash -/

section crash
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
variable [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]

/-- The new generation's file at `p`, in the history `V'`: none, or the file of the inode `p`
names, whole, as the crash left it: on disk (`osFileStart`); never a directory. -/
def startAt (L' : GooseLocalGS GF) (p : GoString) (R : Roots) (V' : Hist) (fo : Option OsFile) :
    IProp GF :=
  match lookupH R V' p with
  | some (.file i) => iprop(∃ f, ⌜fo = some f⌝ ∗ osFileStart (L := L') i f)
  | none => iprop(⌜fo = none⌝)
  | some (.dir _) => iprop(False)

/-- What a crash of the old generation's state `s` leaves: the file's crash, through the runs, if
there is a file. -/
def CrashFileR : CFile → Option OsFile → Prop
  | none, _ => True
  | some (_, x), fo => FileCrashedR (fMeta x) (fRuns x) fo


/-- **The file after a crash**, from the invariant's halves of the old generation's state `s` and
of the claim on `b` (history `h`): what the new tree names at `p` (`crashRest_region'`), and the
file there, whole, `Good`; the old halves come back, so that the invariant can be closed again.
The new generation's tree resources stay in the restart's (`crashRest_treeS'` takes them). -/
theorem cfInv_crash_keep (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF) (D : List Ino)
    (tt : Bool) (V' : Hist) (p : GoString) (R : Roots) (Good : Option OsFile → Prop) (s : CFile)
    (j : Ino) (b : GoString) (h : NamesH) (E : CoPset) (hE : ↑osShN ⊆ E)
    (hfa : FileAt R p j b) (hD : ∀ i, cIno s = some i → i ∉ D) (hok : CrashOk Good j b s h) :
    ⊢ osSharedInv (L := L) R -∗ crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D tt V' -∗
      invRes (L := L) s -∗ osNames (L := L) j (.only [b]) (DFrac.own (1 : Qp).half) h ={E}=∗
      ∃ fo, ⌜Good fo⌝ ∗ startAt L' p R V' fo ∗
        (∃ D', crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D' tt V') ∗
        invRes (L := L) s ∗ osNames (L := L) j (.only [b]) (DFrac.own (1 : Qp).half) h := by
  iintro #Hsi Hr Hs Hn
  imod osCommitLb_zero (L := L) with #Hlb
  imod crashRest_region' Q L L' D tt V' R [((j, .only [b], h), DFrac.own (1 : Qp).half)] 0 E hE
    $$ Hsi Hr [Hn] Hlb with ⟨%hc, Hr, Hcl⟩
  · unfold osClaims; iapply BigSepL.bigSepL_singleton.2; iexact Hn
  unfold osClaims
  icases BigSepL.bigSepL_singleton.1 $$ Hcl with Hn
  obtain ⟨K, -, -, hv⟩ := hc
  have hent : V'.now.entry j b = h.valAfter j K b :=
    hv _ (List.mem_singleton_self _) b (by simp [NameSet.Mem])
  have hlk : lookupH R V' p = h.valAfter j K b := by rw [lookupH_fileAt hfa, hent]
  have hto := hok.1 K
  imodintro
  rcases s with _ | ⟨i, m, bs, _ | ⟨t, off, data, n⟩⟩
  · -- no file at `p`: `p` names nothing after the crash
    rcases hto with ⟨hn, hg⟩ | ⟨i, hi, -⟩
    · iexists none
      iframe Hn Hs
      isplitr
      · ipureintro; exact hg
      isplitr
      · unfold startAt; rw [hlk, hn]; ipureintro; rfl
      iexists D; iexact Hr
    · cases hi
  · -- idle
    dsimp only [invRes]
    icases Hs with ⟨Hm, Hb⟩
    icases osCrash_take_runs_keep Q L L' D tt V' i (hD i rfl) _ m [(0, DFrac.own (1 : Qp).half, bs)]
      $$ Hr Hm [Hb] with ⟨%fo, %hfo, Hf, Hr, Hm, Hb⟩
    · iapply BigSepL.bigSepL_singleton.2; iexact Hb
    icases BigSepL.bigSepL_singleton.1 $$ Hb with Hb
    obtain ⟨hfc, hnm, -⟩ := hfo
    rcases hto with ⟨hn, hg⟩ | ⟨i', hi, hl⟩
    · iexists none
      iframe Hn Hm Hb
      isplitr
      · ipureintro; exact hg
      isplitr
      · unfold startAt; rw [hlk, hn]; ipureintro; rfl
      iexists (i :: D); iexact Hr
    · cases hi
      obtain ⟨f, rfl⟩ := Option.isSome_iff_exists.1 (hnm ⟨j, b, hent.trans hl⟩)
      iexists (some f)
      iframe Hn Hm Hb
      isplitr
      · ipureintro
        exact hok.2 i _ rfl f hfc
      isplitl [Hf]
      · unfold startAt; rw [hlk, hl]; iexists f; isplitr
        · ipureintro; rfl
        unfold osFileStartO; iexact Hf
      iexists (i :: D); iexact Hr
  · -- a write in flight
    dsimp only [invRes]
    icases Hs with ⟨Ht0, Hb1, Hb2⟩
    dsimp only [pwTok]
    icases Ht0 with ⟨Ht0, %hgap⟩
    icases osCrash_take_tok_keep Q L L' D tt V' t _ (hD i rfl)
      [(0, DFrac.own (1 : Qp).half, bs.take (cfLo m off)),
       (cfHi m off data.length, DFrac.own (1 : Qp).half, bs.drop (cfHi m off data.length))]
      $$ Hr Ht0 [Hb1 Hb2] with ⟨%fo, %hfo, Hf, Hr, Ht0, Hbs⟩
    · iapply BigSepL.bigSepL_cons.2; iframe Hb1
      iapply BigSepL.bigSepL_singleton.2; iexact Hb2
    icases BigSepL.bigSepL_cons.1 $$ Hbs with ⟨Hb1, Hbs⟩
    icases BigSepL.bigSepL_singleton.1 $$ Hbs with Hb2
    obtain ⟨hfc, hnm, -⟩ := hfo
    rcases hto with ⟨hn, hg⟩ | ⟨i', hi, hl⟩
    · iexists none
      iframe Hn
      isplitr
      · ipureintro; exact hg
      isplitr
      · unfold startAt; rw [hlk, hn]; ipureintro; rfl
      isplitl [Hr]
      · iexists _; iexact Hr
      iframe; ipureintro; exact hgap
    · cases hi
      obtain ⟨f, rfl⟩ := Option.isSome_iff_exists.1 (hnm ⟨j, b, hent.trans hl⟩)
      iexists (some f)
      iframe Hn
      isplitr
      · ipureintro
        exact hok.2 i _ rfl f hfc
      isplitl [Hf]
      · unfold startAt; rw [hlk, hl]; iexists f; isplitr
        · ipureintro; rfl
        unfold osFileStartO; iexact Hf
      isplitl [Hr]
      · iexists _; iexact Hr
      iframe; ipureintro; exact hgap

end crash

end Perennial
