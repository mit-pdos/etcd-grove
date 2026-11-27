/-
**Database files and free names that survive a crash** (D6-T6, P7, 2026-11-25; `notes/etcd-dist-d6.md`
§T6, rounds 3 and 4). Lean-first. A defs module: the vocabulary the snapshot directory's invariant
(`snapDirInvH`, `Proof/.../rafthttp/Net.lean`) keeps its files and free names in across a crash, and the
crash lemmas over the file extension's restart resources (`crashRest`).

* `CrashLeaves h j b P n` (pure): every crash keeping the claim's entries below `n` leaves the name `b`
  of the directory `j` satisfying `P` (`NamesH.valAfter`, what `RegionCrashed` concludes);
  `nameCrash h j b P` holds it with a lower bound `osCommitLb n` of the committed prefix. A durable
  name (`P = (· = cur)`) follows from a commit at or past every entry (`crashLeaves_of_coh`, with the
  claim's coherence `HistCoh`); a generation's fresh claim (nothing logged) is durable at `0`.
  `nameCrash_crash`: after a crash, the new tree's entry satisfies `P`.
* `fileHoldsMDur i D`: bbolt's `fileHoldsM i D` with every byte durable (`durB`) and the size's crash
  bounds collapsed (`lo = hi = size`), written over bbolt's public API (`boltImage`, `boltImageRcpt`), so
  no new bbolt law is needed for it (`fileHoldsMDur_holds`, by `fileHoldsM_of_image`).
  `fileHoldsMDur_crash`: a file the new tree names comes back whole at the new generation.
* `fileAtCrash path D P` (`fileAtF` with the name's `nameCrash (P i)` and the file `fileHoldsMDur`):
  `fileAtDur` (the name durable, `P i v := v = some (.file i)`) and `fileAtPend` (linked, the directory
  not yet synced: `v = none ∨ v = some (.file i)`); `fileFreeDur path` (`fileFreeF` with
  `nameCrash (· = none)`). Each gives today's `fileAt`/`fileFree` (`fileAtCrash_fileAt`,
  `fileFreeDur_fileFree`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt
public import GooseLang.Ext.Fs.TreeSharedCrash
public import GooseLang.Ext.Fs.TreeSharedCoh
public import GooseLang.Ext.Fs.TreeCommit
public import Proof.os.CrashFile

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode Fs

/-! ### What a crash leaves of a name (pure) -/

section pure
variable [GooseExts]

/-- **Every crash keeping the claim's entries below `n` leaves `b` satisfying `P`** (see the file
header). -/
def CrashLeaves (h : NamesH) (j : Ino) (b : GoString) (P : Option Node → Prop) (n : Nat) : Prop :=
  ∀ K : Nat → Prop, (∀ xe ∈ h.ents, xe.1 < n → K xe.1) → P (h.valAfter j K b)

/-- What a region concludes of a crash (one claim on `b`, the committed bound `n`) meets `CrashLeaves`. -/
theorem crashLeaves_entry {h : NamesH} {j : Ino} {b : GoString} {P : Option Node → Prop} {n : Nat}
    {m' : Tree} (hc : CrashLeaves h j b P n) (hr : RegionCrashed [(j, .only [b], h)] n m') :
    P (m'.entry j b) := by
  obtain ⟨K, -, hK, hv⟩ := hr
  have hmem : ((j, .only [b], h) : Claim) ∈ [(j, .only [b], h)] := List.mem_singleton_self _
  rw [hv _ hmem b (by simp [NameSet.Mem])]
  exact hc K (fun xe hxe hlt => hK _ hmem xe.1 xe.2.1 xe.2.2 hxe hlt)

/-- A coherent claim committed past all its entries is durable: every crash leaves it as it is now. -/
theorem crashLeaves_of_coh {h : NamesH} {j : Ino} {N : NameSet} {b : GoString} {n : Nat}
    (hc : HistCoh h j N) (hb : N.Mem b) (hn : ∀ xe ∈ h.ents, xe.1 < n) :
    CrashLeaves h j b (· = h.cur !! b) n :=
  fun K hK => hc.2 K (fun xe hxe => hK xe hxe (hn xe hxe)) b hb

/-- A generation's fresh claim on `b` (nothing logged) is durable at `0`. -/
theorem crashLeaves_fresh (V : Hist) (hV : V.2 = []) (j : Ino) (b : GoString) :
    CrashLeaves (namesOf V j (.only [b])) j b (· = V.now.entry j b) 0 :=
  fun K _ => namesOf_nil_valAfter V hV j b K

theorem crashLeaves_mono {h : NamesH} {j : Ino} {b : GoString} {P P' : Option Node → Prop} {n : Nat}
    (hc : CrashLeaves h j b P n) (hP : ∀ v, P v → P' v) : CrashLeaves h j b P' n :=
  fun K hK => hP _ (hc K hK)

/-- A crash leaves the bytes of a file whose bytes are all durable and whose size cannot move. -/
theorem fileCrashed_dur {m : OsMeta} {dq : DFrac} {bs : List w8} {f : OsFile}
    (hlo : m.lo = bs.length) (hhi : m.hi = bs.length)
    (hc : FileCrashedR m [(0, dq, bs.map durB)] (some f)) : f.contents = bs := by
  obtain ⟨-, h1, h2, hr, -, -⟩ := hc f rfl
  have hs : f.size = bs.length := by omega
  apply List.ext_getElem
  · simp [OsFile.contents, hs]
  · intro k hk1 hk2
    simp only [OsFile.contents, List.getElem_map, List.getElem_range]
    have hk : k < (bs.map durB).length := by simpa using hk2
    rcases hr _ (List.mem_singleton_self _) k hk (by simp; omega) with ⟨s, hs'⟩ | ⟨hl, -⟩
    · simp only [List.getElem_map, List.mem_singleton, Prod.mk.injEq] at hs'
      simpa using hs'.1
    · simp at hk hl; omega

end pure

/-! ### Durable names and files -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **What every crash leaves of the name `b`**, held against a committed bound (see the file header;
persistent). -/
def nameCrash (h : NamesH) (j : Ino) (b : GoString) (P : Option Node → Prop) : IProp GF :=
  iprop(∃ n : Nat, osCommitLb n ∗ ⌜CrashLeaves h j b P n⌝)

instance nameCrash_persistent (h : NamesH) (j : Ino) (b : GoString) (P : Option Node → Prop) :
    Persistent (nameCrash (GF := GF) h j b P) := by
  unfold nameCrash osCommitLb; infer_instance

/-- **The file of inode `i` holds `D`, mappable, every byte durable** (see the file header). -/
def fileHoldsMDur (i : Ino) (D : Data) : IProp GF :=
  iprop(∃ (m : OsMeta) (bs : List w8), osMeta i (DFrac.own 1) m ∗
    osBytes i 0 (DFrac.own 1) (bs.map durB) ∗
    ⌜m.maps = ∅ ∧ m.size = bs.length ∧ m.lo = bs.length ∧ m.hi = bs.length ∧ bbolt.boltImage bs D ∧
      bs.length ≤ bbolt.boltMaxMapSize⌝ ∗ bbolt.boltImageRcpt bs)

/-- A durable file holds its data, mappable (`fileHoldsM_of_image`). -/
theorem fileHoldsMDur_holds (i : Ino) (D : Data) :
    fileHoldsMDur (GF := GF) i D ⊢ bbolt.fileHoldsM i D := by
  unfold fileHoldsMDur
  iintro ⟨%m, %bs, Hm, Hb, %h, Hr⟩
  obtain ⟨hmaps, hsize, -, -, himg, hlen⟩ := h
  have hfst : (bs.map durB).map Prod.fst = bs := by simp [List.map_map, Function.comp_def]
  iapply bbolt.fileHoldsM_of_image i m (bs.map durB) D hmaps (by simpa using hsize)
    (by rw [hfst]; exact himg) (by simpa using hlen)
  iframe Hm Hb
  rw [hfst]; iexact Hr

/-- **A durable file, or one about to be, at `path`** (see the file header), at the instances: the claim
on the name `b` of the directory `d` (with `d`'s path and a share of its call permission), naming the
inode `i`, what every crash leaves of it (`P i`), and the file `fileHoldsMDur`. -/
def fileAtCrashF (path : GoString) (D : Data) (P : Ino → Option Node → Prop) : IProp GF :=
  iprop(∃ (R : Roots) (d b : GoString) (dq : DFrac) (j : Ino) (qc : Qp) (h : NamesH) (i : Ino),
    ⌜path = child d b ∧ NameOk b ∧ h.cur !! b = some (.file i) ∧ PathFits path⌝ ∗ osInv ∗
    osSharedInv R ∗ osPathS R d dq j ∗ osCallPerm (callKey R d) qc ∗
    osNames j (.only [b]) (DFrac.own 1) h ∗ nameCrash h j b (P i) ∗ fileHoldsMDur i D)

/-- **The name `path` is free, after every crash too**, at the instances. -/
def fileFreeDurF (path : GoString) : IProp GF :=
  iprop(∃ (R : Roots) (d b : GoString) (dq : DFrac) (j : Ino) (qc : Qp) (h : NamesH),
    ⌜path = child d b ∧ NameOk b ∧ h.cur !! b = none ∧ PathFits path⌝ ∗ osInv ∗ osSharedInv R ∗
    osPathS R d dq j ∗ osCallPerm (callKey R d) qc ∗ osNames j (.only [b]) (DFrac.own 1) h ∗
    nameCrash h j b (· = none))

theorem fileAtCrashF_fileAtF (path : GoString) (D : Data) (P : Ino → Option Node → Prop) :
    fileAtCrashF (GF := GF) path D P ⊢ fileAtF path D := by
  unfold fileAtCrashF fileAtF nameAtF
  iintro ⟨%R, %d, %b, %dq, %j, %qc, %h, %i, %hp, #Hinv, #Hsh, Hp, Hc, Hn, -, Hf⟩
  iexists i
  isplitr [Hf]
  · iexists R, d, b, dq, j, qc, h
    iframe Hp Hc Hn Hinv Hsh
    ipureintro; exact hp
  iapply fileHoldsMDur_holds $$ Hf

theorem fileFreeDurF_fileFreeF (path : GoString) :
    fileFreeDurF (GF := GF) path ⊢ fileFreeF path := by
  unfold fileFreeDurF fileFreeF
  iintro ⟨%R, %d, %b, %dq, %j, %qc, %h, %hp, #Hinv, #Hsh, Hp, Hc, Hn, -⟩
  iexists R, d, b, dq, j, qc, h
  iframe Hp Hc Hn Hinv Hsh
  ipureintro; exact hp

end defs

section wrapped
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- What a crash leaves of a durable file's name: the file. -/
def durNamed (i : Ino) (v : Option Node) : Prop := v = some (.file i)

/-- What a crash leaves of a linked file's name before its directory's sync: nothing or the file. -/
def pendNamed (i : Ino) (v : Option Node) : Prop := v = none ∨ v = some (.file i)

/-- **The file at `path` holds `D`, durably** (exclusive; see the file header). -/
def fileAtDur (path : GoString) (D : Data) : IProp GF := onFs (fileAtCrashF path D durNamed)

/-- **The file at `path` holds `D`, its bytes durable, its name not yet** (exclusive). -/
def fileAtPend (path : GoString) (D : Data) : IProp GF := onFs (fileAtCrashF path D pendNamed)

/-- **The name `path` is free, after every crash too** (exclusive). -/
def fileFreeDur (path : GoString) : IProp GF := onFs (fileFreeDurF path)

theorem fileAtDur_fileAt (path : GoString) (D : Data) :
    fileAtDur (GF := GF) path D ⊢ fileAt path D := by
  unfold fileAtDur fileAt
  cases hc : theFs GF with
  | none => rw [onFs_none hc, onFs_none hc]
  | some c => rw [onFs_some hc, onFs_some hc]; exact @fileAtCrashF_fileAtF _ _ _ _ c.S c.ok c.has _ _ _ _ _ _ _

theorem fileAtPend_fileAt (path : GoString) (D : Data) :
    fileAtPend (GF := GF) path D ⊢ fileAt path D := by
  unfold fileAtPend fileAt
  cases hc : theFs GF with
  | none => rw [onFs_none hc, onFs_none hc]
  | some c => rw [onFs_some hc, onFs_some hc]; exact @fileAtCrashF_fileAtF _ _ _ _ c.S c.ok c.has _ _ _ _ _ _ _

theorem fileFreeDur_fileFree (path : GoString) :
    fileFreeDur (GF := GF) path ⊢ fileFree path := by
  unfold fileFreeDur fileFree
  cases hc : theFs GF with
  | none => rw [onFs_none hc, onFs_none hc]
  | some c => rw [onFs_some hc, onFs_some hc]; exact @fileFreeDurF_fileFreeF _ _ _ _ c.S c.ok c.has _ _ _ _ _

end wrapped

/-! ### After a crash -/

section crash
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]

/-- **What a crash left at a name** whose claim the old generation `L` held, with `nameCrash`: an entry
satisfying `P`. The claim comes back, so that an invariant holding it can be closed again. -/
theorem nameCrash_crash (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF) (D : List Ino)
    (tt : Bool) (V' : Hist) (R : Roots) (j : Ino) (b : GoString) (dq : DFrac) (h : NamesH)
    (P : Option Node → Prop) (E : CoPset) (hE : ↑osShN ⊆ E) :
    ⊢ osSharedInv (L := L) R -∗ crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D tt V' -∗
      osNames (L := L) j (.only [b]) dq h -∗ nameCrash (hG := ⟨G, L⟩) h j b P ={E}=∗
      ⌜P (V'.now.entry j b)⌝ ∗ crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D tt V' ∗
      osNames (L := L) j (.only [b]) dq h := by
  unfold nameCrash
  iintro #Hsi Hr Hn ⟨%n, #Hlb, %hc⟩
  imod crashRest_region' Q L L' D tt V' R [((j, .only [b], h), dq)] n E hE $$ Hsi Hr [Hn] Hlb
    with ⟨%hrc, Hr, Hcl⟩
  · unfold osClaims; iapply BigSepL.bigSepL_singleton.2; iexact Hn
  unfold osClaims
  icases BigSepL.bigSepL_singleton.1 $$ Hcl with Hn
  imodintro
  iframe Hr Hn
  ipureintro
  exact crashLeaves_entry hc hrc

/-- **A durable file the new tree names, at the new generation** (`osCrash_take_runs_keep`): whole, its
bytes as they were (durable, the size fixed), now as the new generation starts with it. -/
theorem fileHoldsMDur_crash (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF) (D : List Ino)
    (tt : Bool) (V' : Hist) (i : Ino) (hi : i ∉ D) (hn : Named V'.now i) (Dt : Data) :
    ⊢ crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D tt V' -∗
      fileHoldsMDur (hG := ⟨G, L⟩) i Dt -∗
      fileHoldsMDur (hG := ⟨G, L'⟩) i Dt ∗
        crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) (i :: D) tt V' := by
  unfold fileHoldsMDur
  iintro Hr ⟨%m, %bs, Hm, Hb, %hm, Hrc⟩
  obtain ⟨hmaps, hsize, hlo, hhi, himg, hlen⟩ := hm
  icases osCrash_take_runs_keep Q L L' D tt V' i hi (DFrac.own 1) m [(0, DFrac.own 1, bs.map durB)]
    $$ Hr Hm [Hb] with ⟨%fo, %hfo, Hf, Hr, -, -⟩
  · iapply BigSepL.bigSepL_singleton.2; iexact Hb
  obtain ⟨hfc, hnm, -⟩ := hfo
  obtain ⟨f, rfl⟩ := Option.isSome_iff_exists.1 (hnm hn)
  have hct : f.contents = bs := fileCrashed_dur hlo hhi hfc
  subst hct
  unfold osFileStartO osFileStart
  icases Hf with ⟨Hm', Hb'⟩
  iframe Hr
  iexists initMeta f, f.contents
  iframe Hm' Hb'
  isplitr
  · ipureintro
    have hfs : f.size = f.contents.length := by simp [OsFile.contents]
    exact ⟨rfl, hfs, hfs, hfs, himg, hlen⟩
  iapply bbolt.boltImageRcpt_gen G L L' f.contents $$ Hrc

end crash

end backend
end EtcdGrove
end Perennial
