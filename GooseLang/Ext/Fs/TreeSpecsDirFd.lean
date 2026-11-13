/-
WP specs of the steps on a directory fd (`Impl.lean`): `FdKind` of a directory fd, `DirSync`,
`DirClose`, `DirReadNext`; the query `PathKind` of a path; and the state facts that adding, moving on and removing a directory fd
keep (used by `TreeSpecsOpen.lean` too). A directory fd holds a fraction of the tree's history from its
open to its close (`rdRes`), of which its phase's view `g` is the directory's (`dview`). Untrusted.
-/
module

public import GooseLang.Ext.Fs.TreeSpecs

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-! ## Pure facts -/

/-- The tree now is the history's. -/
theorem tree_hist {st : OsState} {V : Hist} (hV : V = (st.fs.treeDur, st.fs.metaLog)) :
    st.tree = V.now := by subst hV; rfl

/-- The names of a well-formed tree are valid. -/
theorem entry_nameOk {st : OsState} (hw : FsTreeWf st) {j : Ino} {b : GoString} {n : Node}
    (h : st.tree.entry j b = some n) : NameOk b := by
  have := (hw.hist st.fs.metaLog.length (Nat.le_refl _)).1
  rw [List.take_length] at this
  exact (this.2.2.1 j b n h).1

/-- The names a read begun now sees: the directory's entries (whose names are valid). -/
theorem present_eq {st : OsState} {j : Ino} {g : DirG}
    (h : entsOf st.tree j = g.now) (b : GoString) :
    present st j b = (decide (NameOk b) && (g.now !! b).isSome) := by
  unfold present
  rw [← h, entsOf_lookup]

theorem isSome_nameOk {st : OsState} (hw : FsTreeWf st) {j : Ino} {g : DirG}
    (h : entsOf st.tree j = g.now) {b : GoString} (hb : (g.now !! b).isSome) : NameOk b := by
  rw [← h, entsOf_lookup] at hb
  cases he : st.tree.entry j b with
  | none => rw [he] at hb; cases hb
  | some n => exact entry_nameOk hw he

theorem phOk_idle {g : DirG} {q : Qp} {rd : OsDirRead} (h : PhOk (.idle g q) rd) : rd = .idle := by
  cases rd <;> simp_all [PhOk]

theorem phOk_reading {rs : List GoString} {g : DirG} {q : Qp} {rd : OsDirRead}
    (h : PhOk (.reading rs g q) rd) : ∃ u s r, rd = .reading u s r ∧
      ∀ b, u b = (decide (NameOk b) && (g.now !! b).isSome) ∧
        s b = (decide (NameOk b) && (g.now !! b).isSome) ∧ r b = decide (b ∈ rs) := by
  cases rd with
  | reading u s r => exact ⟨u, s, r, rfl, h⟩
  | _ => simp [PhOk] at h

/-- The state with the directory fd `fd` set to `df'`. -/
abbrev setDfd (st : OsState) (fd : w64) (df' : OsDirFd) : OsState :=
  st.setProc { st.proc with dfds := <[fd := df']> st.proc.dfds }

theorem filesSame_setDfd (st : OsState) (fd : w64) (df' : OsDirFd) :
    FilesSame st (setDfd st fd df') := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A directory fd set (added, or its read moved on), on a directory of the tree, at a number no
file fd has: the tree's well-formedness kept. -/
theorem fsTreeWf_setDfd {st : OsState} (hw : FsTreeWf st) {fd : w64} {df' : OsDirFd}
    (hfd : st.proc.fds !! fd = none) (hin : df'.ino ∈ st.tree) :
    FsTreeWf (setDfd st fd df') := by
  refine ⟨hw.roots, hw.hist, fun fd' df'' h' => ?_, fun fd' h' => ?_, hw.files_lt⟩
  · have h'' : (<[fd := df']> st.proc.dfds) !! fd' = some df'' := h'
    rw [GMap.lookup_insert_eq_iff] at h''
    split at h''
    · cases h''; exact hin
    · exact hw.dfds fd' df'' h''
  · show (<[fd := df']> st.proc.dfds) !! fd' = none
    rw [GMap.lookup_insert_eq_iff]; split
    · subst_vars; exact absurd hfd h'
    · exact hw.disj fd' h'

/-- ... and the coherence, with the fd's ghost entry. -/
theorem treeCoh_setDfd {st : OsState} {V Γdf Γc} (hc : TreeCoh st V Γdf Γc) {fd : w64}
    {df' : OsDirFd} {x : Ino × DirPh} (hino : x.1 = df'.ino) (hph : PhOk x.2 df'.rd)
    (hrd : x.2.g = dview V x.1) :
    TreeCoh (setDfd st fd df') V (<[fd := x]> Γdf) Γc := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hc
  refine ⟨h1, h2, fun fd' => ?_, fun fd' x' df hx hdf => ?_, fun fd' x' hx => ?_, h6, h7⟩
  · show ((<[fd := x]> Γdf) !! fd').map (·.1) = ((<[fd := df']> st.proc.dfds) !! fd').map (·.ino)
    rw [GMap.lookup_insert_eq_iff, GMap.lookup_insert_eq_iff]; split
    · simp [hino]
    · exact h3 fd'
  · have hdf' : (<[fd := df']> st.proc.dfds) !! fd' = some df := hdf
    rw [GMap.lookup_insert_eq_iff] at hx hdf'
    split at hx
    · rw [if_pos ‹_›] at hdf'; cases hx; cases hdf'; exact hph
    · rw [if_neg ‹_›] at hdf'; exact h4 fd' x' df hx hdf'
  · rw [GMap.lookup_insert_eq_iff] at hx; split at hx
    · cases hx; exact hrd
    · exact h5 fd' x' hx

/-- The state with the directory fd `fd` gone. -/
abbrev delDfd (st : OsState) (fd : w64) : OsState :=
  st.setProc { st.proc with dfds := GMap.delete fd st.proc.dfds }

theorem fsTreeWf_delDfd {st : OsState} (hw : FsTreeWf st) (fd : w64) : FsTreeWf (delDfd st fd) := by
  refine ⟨hw.roots, hw.hist, fun fd' df' h' => ?_, fun fd' h' => ?_, hw.files_lt⟩
  · have h'' : (GMap.delete fd st.proc.dfds) !! fd' = some df' := h'
    rw [GMap.lookup_delete_iff] at h''; split at h''
    · cases h''
    · exact hw.dfds fd' df' h''
  · show (GMap.delete fd st.proc.dfds) !! fd' = none
    rw [GMap.lookup_delete_iff]; split
    · rfl
    · exact hw.disj fd' h'

theorem treeCoh_delDfd {st : OsState} {V Γdf Γc} (hc : TreeCoh st V Γdf Γc) (fd : w64) :
    TreeCoh (delDfd st fd) V (GMap.delete fd Γdf) Γc := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hc
  refine ⟨h1, h2, fun fd' => ?_, fun fd' x' df' hx hd => ?_, fun fd' x hx => ?_, h6, h7⟩
  · show ((GMap.delete fd Γdf) !! fd').map (·.1) =
      ((GMap.delete fd st.proc.dfds) !! fd').map (·.ino)
    rw [GMap.lookup_delete_iff, GMap.lookup_delete_iff]; split
    · rfl
    · exact h3 fd'
  · have hx' : Γdf !! fd' = some x' := by
      rw [GMap.lookup_delete_iff] at hx; split at hx
      · cases hx
      · exact hx
    have hd' : st.proc.dfds !! fd' = some df' := by
      have hd'' : (GMap.delete fd st.proc.dfds) !! fd' = some df' := hd
      rw [GMap.lookup_delete_iff] at hd''; split at hd''
      · cases hd''
      · exact hd''
    exact h4 fd' x' df' hx' hd'
  · rw [GMap.lookup_delete_iff] at hx; split at hx
    · cases hx
    · exact h5 fd' x hx

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- The worlds after a step that leaves the files alone, from their parts. -/
theorem worlds_close {st st' : OsState} {Γb Γm Γf Γt} {h h' : GMap Loc (NonAtomic val)} {V : Hist}
    {Γdf : GMap w64 (Ino × DirPh)} {Γc : GMap Nat (Nat × Qp)}
    (hs : FilesSame st st') (hr : HeapRendered st st' h h') (hfr : MapsFresh st st' h)
    (hroots : st'.fs.roots = st.fs.roots) (hw' : FsTreeWf st') (hc' : TreeCoh st' V Γdf Γc) :
    ⊢ osWorld (L := L) st Γb Γm Γf Γt h -∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γd (histMap (st.fs.roots, V)) -∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γdf Γdf -∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γc Γc -∗
      rdRes (gooseOsGS (L := L)) Γdf -∗ callRes (gooseOsGS (L := L)) Γc ==∗
      osWorld (L := L) st' Γb Γm Γf Γt h' ∗ treeWorld (L := L) st' V Γdf Γc := by
  iintro Hw HAd HAdf HAc Hrd Hcr
  imod osWorld_filesSame hs hr hfr $$ Hw with Hw
  imodintro
  iframe Hw
  unfold treeWorld
  rw [hroots]
  iframe
  ipureintro; exact ⟨hw', hc'⟩

/-- **`FdKind(fd)` of a directory fd**: `1`. -/
theorem wp_osFdKindDir (fd : w64) (dq : DFrac) (x : Ino × DirPh) (hE : ↑osN ⊆ E)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osDirFd (L := L) fd dq x -∗
      (osDirFd (L := L) fd dq x -∗ Φ (#(1 : w64))) -∗
      WP (ExternalOp fsExt.name "FdKind" (Val (#fd))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd HΦ
  iapply wp_fs_stepT "FdKind" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %V %Γdf %Γc %h Hw Hn
  unfold treeWorld
  icases Hn with ⟨%Hns, HAd, HAdf, HAc, Hrd, Hcr⟩
  obtain ⟨hw, hc⟩ := Hns
  unfold osDirFd
  icases gAuth_lookup _ _ _ _ _ _ $$ HAdf Hfd with %Hfl
  obtain ⟨df, hdf⟩ : ∃ df, st.proc.dfds !! fd = some df := by
    have := hc.fds fd; rw [Hfl] at this
    cases h0 : st.proc.dfds !! fd with
    | none => rw [h0] at this; cases this
    | some df => exact ⟨df, rfl⟩
  have hnf : st.proc.fds !! fd = none := by
    cases h0 : st.proc.fds !! fd with
    | none => rfl
    | some d => have := hw.disj fd (by rw [h0]; simp); rw [hdf] at this; cases this
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  imodintro
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) Hwc.1 (filesSame_refl st) Hag
    exact ⟨_, h, st, ⟨fd, rfl, rfl, .inr ⟨hnf, ⟨df, hdf⟩, rfl⟩⟩, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨fd', hv, hst, hres⟩ := Hst
  subst st'
  cases go.intoVal_inj hv
  rcases hres with ⟨⟨d, hd⟩, -⟩ | ⟨-, -, rfl⟩
  · rw [hnf] at hd; cases hd
  imod worlds_close (filesSame_refl st) Hr Hfr rfl hw hc $$ [HAb HAm HAf HAt Htok Hcells Hσ]
    HAd HAdf HAc Hrd Hcr with ⟨Hw, Hn⟩
  · unfold osWorld; iframe; ipureintro; exact Hwc
  imodintro
  iexists Γb, Γm, Γf, Γt, V, Γdf, Γc
  try unfold osWorld
  try unfold treeWorld
  try unfold osDirFd
  try unfold rdRes
  isplitl [Hw]
  · iexact Hw
  isplitl [Hn]
  · iexact Hn
  iapply wp_value'
  iapply HΦ; (try unfold osDirFd); iexact Hfd

/-- **`PathKind(p)`**, the query of where a path is, with a fraction of the tree's roots `R` and
history `V`, for a path strictly below a root or at or above one: `#1` for a `TreeName`, `#0`
otherwise; nothing changes. -/
theorem wp_osPathKind (p : GoString) (R : Roots) (V : Hist) (dq : DFrac)
    (hp : (Hist.st R V).TreeName p ∨ (Hist.st R V).AtOrAboveRoot p) (hE : ↑osN ⊆ E)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osTree (L := L) dq R V -∗
      (∀ k : w64, ⌜(Hist.st R V).TreeName p ∧ k = 1 ∨
          ¬ (Hist.st R V).TreeName p ∧ (Hist.st R V).AtOrAboveRoot p ∧ k = 0⌝ -∗
        osTree (L := L) dq R V -∗ Φ (#k)) -∗
      WP (ExternalOp fsExt.name "PathKind" (Val (#p))) @ s; E {{ Φ }} := by
  iintro #Hinv Hh HΦ
  iapply wp_fs_stepT "PathKind" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %V0 %Γdf %Γc %h Hw Hn
  unfold treeWorld
  icases Hn with ⟨%Hns, HAd, HAdf, HAc, Hrd, Hcr⟩
  obtain ⟨hw, hc⟩ := Hns
  icases osTree_auth _ _ _ _ _ $$ HAd Hh with %Heq
  obtain ⟨rfl, rfl⟩ := Heq
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hstep : ∃ e', IsFsStep "PathKind" (#p) st e' st := by
    by_cases ht : st.TreeName p
    · exact ⟨_, p, rfl, rfl, .inl ⟨ht, rfl⟩⟩
    · exact ⟨_, p, rfl, rfl, .inr ⟨ht, hp.resolve_left ht, rfl⟩⟩
  imodintro
  isplitr
  · ipureintro
    obtain ⟨e0, he0⟩ := hstep
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) Hwc.1 (filesSame_refl st) Hag
    exact ⟨_, h, st, he0, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨p', hv, hst, hres⟩ := Hst
  subst st'
  cases go.intoVal_inj hv
  imod worlds_close (filesSame_refl st) Hr Hfr rfl hw hc $$ [HAb HAm HAf HAt Htok Hcells Hσ]
    HAd HAdf HAc Hrd Hcr with ⟨Hw, Hn⟩
  · unfold osWorld; iframe; ipureintro; exact Hwc
  imodintro
  iexists Γb, Γm, Γf, Γt, V, Γdf, Γc
  try unfold osWorld
  try unfold treeWorld
  isplitl [Hw]
  · iexact Hw
  isplitl [Hn]
  · iexact Hn
  rcases hres with ⟨ht, rfl⟩ | ⟨ht, ha, rfl⟩
  · iapply wp_value'
    iapply HΦ $$ %(1 : w64) %(.inl ⟨ht, rfl⟩) Hh
  · iapply wp_value'
    iapply HΦ $$ %(0 : w64) %(.inr ⟨ht, ha, rfl⟩) Hh

/-- **`fsync(2)` of a directory fd**: any errno; the ghost state as it was (a commit only narrows
what a crash may leave). -/
theorem wp_osDirSync (fd : w64) (dq : DFrac) (x : Ino × DirPh) (hE : ↑osN ⊆ E)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osDirFd (L := L) fd dq x -∗
      (∀ e : w64, osDirFd (L := L) fd dq x -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "DirSync" (Val (#fd))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd HΦ
  iapply wp_fs_stepT "DirSync" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %V %Γdf %Γc %h Hw Hn
  unfold treeWorld
  icases Hn with ⟨%Hns, HAd, HAdf, HAc, Hrd, Hcr⟩
  obtain ⟨hw, hc⟩ := Hns
  unfold osDirFd
  icases gAuth_lookup _ _ _ _ _ _ $$ HAdf Hfd with %Hfl
  obtain ⟨df, hdf⟩ : ∃ df, st.proc.dfds !! fd = some df := by
    have := hc.fds fd; rw [Hfl] at this
    cases h0 : st.proc.dfds !! fd with
    | none => rw [h0] at this; cases this
    | some df => exact ⟨df, rfl⟩
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  imodintro
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) Hwc.1 (filesSame_refl st) Hag
    exact ⟨_, h, st, ⟨fd, df, rfl, hdf, .inr ⟨1, by decide, rfl, rfl⟩⟩, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨fd', df', hv, -, hres⟩ := Hst
  cases go.intoVal_inj hv
  -- the state after: `st`, or `st` with more of the log committed
  have hfacts : FilesSame st st' ∧ st'.fs.roots = st.fs.roots ∧ FsTreeWf st' ∧
      TreeCoh st' V Γdf Γc := by
    have hcm : FilesSame st st.commitAll ∧
        st.commitAll.fs.roots = st.fs.roots ∧ FsTreeWf st.commitAll ∧
        TreeCoh st.commitAll V Γdf Γc :=
      ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, ⟨hw.roots, hw.hist, hw.dfds, hw.disj, hw.files_lt⟩,
        hc.congr rfl rfl rfl rfl⟩
    rcases hres with ⟨hst, -⟩ | ⟨e, -, -, hst⟩
    · rw [hst]; exact hcm
    · rw [hst]; exact ⟨filesSame_refl st, rfl, hw, hc⟩
  obtain ⟨hs, hroots, hw', hc'⟩ := hfacts
  imod worlds_close hs Hr Hfr hroots hw' hc' $$ [HAb HAm HAf HAt Htok Hcells Hσ]
    HAd HAdf HAc Hrd Hcr with ⟨Hw, Hn⟩
  · unfold osWorld; iframe; ipureintro; exact Hwc
  imodintro
  iexists Γb, Γm, Γf, Γt, V, Γdf, Γc
  try unfold osWorld
  try unfold treeWorld
  try unfold osDirFd
  try unfold rdRes
  isplitl [Hw]
  · iexact Hw
  isplitl [Hn]
  · iexact Hn
  rcases hres with ⟨-, rfl⟩ | ⟨e, -, rfl, -⟩
  · iapply wp_value'; iapply HΦ $$ %0; (try unfold osDirFd); iexact Hfd
  · iapply wp_value'; iapply HΦ $$ %e; (try unfold osDirFd); iexact Hfd

/-- What closing a directory fd gives back: the fraction of the history it held. -/
def rdBack (x : Ino × DirPh) : IProp GF := osDir (L := L) x.1 (DFrac.own x.2.q) x.2.g

/-- **`close(2)` of a directory fd**, whole: any errno; the fd gone, and its fraction back. -/
theorem wp_osDirClose (fd : w64) (x : Ino × DirPh) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osDirFd (L := L) fd (DFrac.own 1) x -∗
      (∀ e : w64, rdBack (L := L) x -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "DirClose" (Val (#fd))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd HΦ
  iapply wp_fs_stepT "DirClose" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %V %Γdf %Γc %h Hw Hn
  unfold treeWorld
  icases Hn with ⟨%Hns, HAd, HAdf, HAc, Hrd, Hcr⟩
  obtain ⟨hw, hc⟩ := Hns
  unfold osDirFd
  icases gAuth_lookup _ _ _ _ _ _ $$ HAdf Hfd with %Hfl
  obtain ⟨df, hdf⟩ : ∃ df, st.proc.dfds !! fd = some df := by
    have := hc.fds fd; rw [Hfl] at this
    cases h0 : st.proc.dfds !! fd with
    | none => rw [h0] at this; cases this
    | some df => exact ⟨df, rfl⟩
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hs : FilesSame st (delDfd st fd) := ⟨rfl, rfl, rfl, rfl, rfl⟩
  imodintro
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) Hwc.1 hs Hag
    exact ⟨_, h, _, ⟨fd, 0, df, rfl, hdf, rfl, rfl⟩, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨fd', e, df', hv, -, hst, rfl⟩ := Hst
  cases go.intoVal_inj hv
  subst hst
  -- the fd's part of the reads' fractions, back
  unfold rdRes
  icases (BigSepM.bigSepM_delete (M := GMap w64)
    (Φ := fun (_ : w64) (x : Ino × DirPh) => rdPart (gooseOsGS (L := L)) x) Hfl).1 $$ Hrd
    with ⟨Hx, Hrd⟩
  imod gAuth_delete _ _ _ _ _ $$ HAdf Hfd with HAdf
  imod worlds_close hs Hr Hfr rfl (fsTreeWf_delDfd hw fd) (treeCoh_delDfd hc fd)
    $$ [HAb HAm HAf HAt Htok Hcells Hσ] HAd HAdf HAc [Hrd] Hcr with ⟨Hw, Hn⟩
  · unfold osWorld; iframe; ipureintro; exact Hwc
  · unfold rdRes; iexact Hrd
  imodintro
  iexists Γb, Γm, Γf, Γt, V, GMap.delete fd Γdf, Γc
  try unfold osWorld
  try unfold treeWorld
  try unfold osDirFd
  try unfold rdRes
  isplitl [Hw]
  · iexact Hw
  isplitl [Hn]
  · iexact Hn
  iapply wp_value'
  iapply HΦ $$ %e
  unfold rdBack osDir rdPart
  icases Hx with ⟨%RV, Hq, %hg⟩
  iexists RV.1, RV.2
  unfold osTree
  iframe Hq
  ipureintro; exact hg

/-- The values of a step of `Readdirnames`: a name, the end, an errno. -/
abbrev rdName (b : GoString) : val := PairV (#b) (PairV (#(0 : w64)) (#(0 : w64)))
abbrev rdEnd : val := PairV (#([] : GoString)) (PairV (#(1 : w64)) (#(0 : w64)))
abbrev rdErr (e : w64) : val := PairV (#([] : GoString)) (PairV (#(0 : w64)) (#e))

/-- **One step of a read of a directory fd**, its read begun (`rs` the names returned) or about to
be (`fresh`); the fd, on the directory of inode `j`, holds a fraction `q` of the history, of which
`g` is the directory's view: a name of the directory not returned, the end once all were, or an
errno. -/
theorem wp_osDirReadStep (fd : w64) (j : Ino) (rs : List GoString) (g : DirG) (q : Qp)
    (fresh : Bool) (hfr : fresh = true → rs = []) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗
      osDirFd (L := L) fd (DFrac.own 1) (j, if fresh then .idle g q else .reading rs g q) -∗
      (∀ v, ((∃ b, ⌜v = rdName b ∧ (g.now !! b).isSome ∧ b ∉ rs⌝ ∗
              osDirFd (L := L) fd (DFrac.own 1) (j, .reading (b :: rs) g q)) ∨
            (⌜v = rdEnd ∧ ∀ b, (g.now !! b).isSome → b ∈ rs⌝ ∗
              osDirFd (L := L) fd (DFrac.own 1) (j, .done g q)) ∨
            (∃ e : w64, ⌜e ≠ 0 ∧ v = rdErr e⌝ ∗
              osDirFd (L := L) fd (DFrac.own 1) (j, .reading rs g q))) -∗ Φ v) -∗
      WP (ExternalOp fsExt.name "DirReadNext" (Val (#fd))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd HΦ
  iapply wp_fs_stepT "DirReadNext" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %V %Γdf %Γc %h Hw Hn
  unfold treeWorld
  icases Hn with ⟨%Hns, HAd, HAdf, HAc, Hrd, Hcr⟩
  obtain ⟨hw, hc⟩ := Hns
  unfold osDirFd
  icases gAuth_lookup _ _ _ _ _ _ $$ HAdf Hfd with %Hfl
  obtain ⟨df, hdf⟩ : ∃ df, st.proc.dfds !! fd = some df := by
    have := hc.fds fd; rw [Hfl] at this
    cases h0 : st.proc.dfds !! fd with
    | none => rw [h0] at this; cases this
    | some df => exact ⟨df, rfl⟩
  have hino : df.ino = j := by
    have := hc.fds fd; rw [Hfl, hdf] at this; simpa using this.symm
  have hph := hc.ph fd _ df Hfl hdf
  have Hdl : g = dview V j := by
    have := hc.rd fd _ Hfl; cases fresh <;> exact this
  have hents : entsOf st.tree j = g.now := by rw [Hdl, dview_now, tree_hist hc.hist]
  have hcur : ∃ u s r,
      df.rd.cur st df.ino = some (u, s, r) ∧
      ∀ b, u b = (decide (NameOk b) && (g.now !! b).isSome) ∧
        s b = (decide (NameOk b) && (g.now !! b).isSome) ∧ r b = decide (b ∈ rs) := by
    cases fresh with
    | true =>
      have hrd := phOk_idle hph
      refine ⟨present st j, present st j, fun _ => false, by rw [hrd, hino]; rfl,
        fun b => ⟨present_eq hents b, present_eq hents b, ?_⟩⟩
      rw [hfr rfl]; simp
    | false =>
      obtain ⟨u, s, r, hrd, hus⟩ := phOk_reading hph
      exact ⟨u, s, r, by rw [hrd]; rfl, hus⟩
  obtain ⟨u, s, r, hcur', hus⟩ := hcur
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hnf : st.proc.fds !! fd = none := by
    cases h0 : st.proc.fds !! fd with
    | none => rfl
    | some d => have := hw.disj fd (by rw [h0]; simp); rw [hdf] at this; cases this
  have hin : df.ino ∈ st.tree := hw.dfds fd df hdf
  imodintro
  isplitr
  · ipureintro
    obtain ⟨hfr', hr⟩ := step_filesSame (h := h) Hwc.1
      (filesSame_setDfd st fd { df with rd := .reading u s r }) Hag
    exact ⟨_, h, _, ⟨fd, df, u, s, r, rfl, hdf, hcur', .inr (.inr ⟨1, by decide, rfl, rfl⟩)⟩,
      hfr', hr⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr', Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨fd', df', u', s', r', hv, hdf', hcur'', hres⟩ := Hst
  cases go.intoVal_inj hv
  rw [hdf] at hdf'; cases hdf'
  rw [hcur'] at hcur''; cases hcur''
  -- the reads' fractions, with the fd's entry swapped
  unfold rdRes
  icases (BigSepM.bigSepM_insert_acc (M := GMap w64)
    (Φ := fun (_ : w64) (x : Ino × DirPh) => rdPart (gooseOsGS (L := L)) x) Hfl) $$ Hrd
    with ⟨Hx, Hrd⟩
  ihave Hq : iprop(∃ RV : Roots × Hist, gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γd ()
      (DFrac.own q) RV ∗ ⌜g = dview RV.2 j⌝) $$ [Hx]
  · unfold rdPart
    cases fresh <;> (simp only [Bool.false_eq_true, ↓reduceIte, DirPh.q, DirPh.g] at *; iexact Hx)
  -- the fd's ghost entry, to the new phase
  have hfinish : ∀ (rd' : OsDirRead) (ph' : DirPh), PhOk ph' rd' → ph'.g = dview V j →
      st' = setDfd st fd { df with rd := rd' } →
      ⊢ osWorld (L := L) st Γb Γm Γf Γt h -∗
        gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γd (histMap (st.fs.roots, V)) -∗
        gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γdf Γdf -∗
        gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γdf fd (DFrac.own 1)
          (j, if fresh then DirPh.idle g q else .reading rs g q) -∗
        gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γc Γc -∗
        ([∗map] k ↦ v ∈ <[fd := (j, ph')]> Γdf, rdPart (gooseOsGS (L := L)) v) -∗
        callRes (gooseOsGS (L := L)) Γc ==∗
        osWorld (L := L) st' Γb Γm Γf Γt h' ∗ treeWorld (L := L) st' V (<[fd := (j, ph')]> Γdf) Γc ∗
        osDirFd (L := L) fd (DFrac.own 1) (j, ph') := by
    intro rd' ph' hok hrd hst
    subst hst
    have hw' := fsTreeWf_setDfd hw (df' := { df with rd := rd' }) hnf hin
    have hc' := treeCoh_setDfd (fd := fd) (df' := { df with rd := rd' }) (x := (j, ph')) hc
      hino.symm hok hrd
    iintro Hw HAd HAdf Hfd HAc Hrd Hcr
    imod gAuth_update _ _ _ _ _ (j, ph') $$ HAdf Hfd with ⟨HAdf, Hfd⟩
    imod worlds_close (filesSame_setDfd st fd _) Hr Hfr' rfl hw' hc' $$ Hw HAd HAdf HAc [Hrd] Hcr
      with ⟨Hw, Hn⟩
    · unfold rdRes; iexact Hrd
    imodintro
    try unfold osWorld
    try unfold treeWorld
    try unfold osDirFd
    try unfold rdRes
    isplitl [Hw]
    · iexact Hw
    isplitl [Hn]
    · iexact Hn
    (try unfold osDirFd); iexact Hfd
  ihave Hw : osWorld (L := L) st Γb Γm Γf Γt h $$ [HAb HAm HAf HAt Htok Hcells Hσ]
  · unfold osWorld; iframe; ipureintro; exact Hwc
  rcases hres with ⟨b, hsb, hrb, hst, rfl⟩ | ⟨hall, hst, rfl⟩ | ⟨e, he, hst, rfl⟩
  · -- a name
    have hb : (g.now !! b).isSome := by
      have := (hus b).2.1; rw [hsb] at this
      simp only [Bool.true_eq, Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.2
    have hbr : b ∉ rs := by
      intro hm; have := (hus b).2.2; rw [hrb] at this; simp [hm] at this
    have hok : PhOk (.reading (b :: rs) g q) (.reading u s (fun x => r x || decide (x = b))) := by
      intro x
      refine ⟨(hus x).1, (hus x).2.1, ?_⟩
      show (r x || decide (x = b)) = _
      rw [(hus x).2.2]; by_cases hx : x = b <;> simp [hx]
    ihave Hrd := Hrd $$ %(j, .reading (b :: rs) g q) [Hq]
    · unfold rdPart; dsimp only [DirPh.q, DirPh.g]; iexact Hq
    imod hfinish _ _ hok Hdl hst $$ Hw HAd HAdf Hfd HAc Hrd Hcr with ⟨Hw, Hn, Hfd⟩
    imodintro
    iexists Γb, Γm, Γf, Γt, V, (<[fd := (j, .reading (b :: rs) g q)]> Γdf), Γc
    try unfold osWorld
    try unfold treeWorld
    try unfold osDirFd
    try unfold rdRes
    isplitl [Hw]
    · iexact Hw
    isplitl [Hn]
    · iexact Hn
    iapply wp_value'
    iapply HΦ
    ileft; iexists b; iframe Hfd; ipureintro; exact ⟨rfl, hb, hbr⟩
  · -- the end: every name returned
    have hall' : ∀ b, (g.now !! b).isSome → b ∈ rs := by
      intro b hb
      have hbn : NameOk b := isSome_nameOk hw hents hb
      have hu : u b = true := by rw [(hus b).1]; simp [hbn, hb]
      have hp : present st df.ino b = true := by rw [hino, present_eq hents b]; simp [hbn, hb]
      have := hall b hu hp
      rw [(hus b).2.2] at this; simpa using this
    ihave Hrd := Hrd $$ %(j, DirPh.done g q) [Hq]
    · unfold rdPart; dsimp only [DirPh.q, DirPh.g]; iexact Hq
    imod hfinish _ _ (by trivial : PhOk (.done g q) .done) Hdl hst $$ Hw HAd HAdf Hfd HAc Hrd Hcr
      with ⟨Hw, Hn, Hfd⟩
    imodintro
    iexists Γb, Γm, Γf, Γt, V, (<[fd := (j, .done g q)]> Γdf), Γc
    try unfold osWorld
    try unfold treeWorld
    try unfold osDirFd
    try unfold rdRes
    isplitl [Hw]
    · iexact Hw
    isplitl [Hn]
    · iexact Hn
    iapply wp_value'
    iapply HΦ
    iright; ileft; iframe Hfd; ipureintro; exact ⟨rfl, hall'⟩
  · -- an errno: the read begun, nothing returned
    have hok : PhOk (.reading rs g q) (.reading u s r) := fun x => hus x
    ihave Hrd := Hrd $$ %(j, .reading rs g q) [Hq]
    · unfold rdPart; dsimp only [DirPh.q, DirPh.g]; iexact Hq
    imod hfinish _ _ hok Hdl hst $$ Hw HAd HAdf Hfd HAc Hrd Hcr with ⟨Hw, Hn, Hfd⟩
    imodintro
    iexists Γb, Γm, Γf, Γt, V, (<[fd := (j, .reading rs g q)]> Γdf), Γc
    try unfold osWorld
    try unfold treeWorld
    try unfold osDirFd
    try unfold rdRes
    isplitl [Hw]
    · iexact Hw
    isplitl [Hn]
    · iexact Hn
    iapply wp_value'
    iapply HΦ
    iright; iright; iexists e; iframe Hfd; ipureintro; exact ⟨he, rfl⟩

end specs

end Fs
end Perennial

end
