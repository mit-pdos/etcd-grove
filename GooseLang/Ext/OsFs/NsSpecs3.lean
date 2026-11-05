/-
WP specs of the namespace's opens and directory reads (`NsSpecs.lean`, `NsSpecs2.lean`).
Untrusted.
-/
module

public import GooseLang.Ext.OsFs.NsSpecs2

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode
open goose_heap

/-! ## Pure facts -/

/-- `O_RDONLY | O_CLOEXEC`, as `os.OpenFile`'s model passes `O_RDONLY`. -/
abbrev flRO : w64 := W64 0x80000
/-- `O_RDWR | O_CREAT | O_CLOEXEC`. -/
abbrev flCreat : w64 := W64 0x80042

theorem flRO_ok : OpenFlagsOk flRO.toNat := by
  simp only [OpenFlagsOk, O_CREAT, O_TRUNC, O_CLOEXEC]; decide
theorem flCreat_ok : OpenFlagsOk flCreat.toNat := by
  simp only [OpenFlagsOk, O_CREAT, O_TRUNC, O_CLOEXEC]; decide

/-- A new directory fd keeps the namespace's well-formedness... -/
theorem nsWf_addDirFd {st : OsState} (hw : NsWf st) {fd : w64} {d : GoString}
    (hfd : st.fds !! fd = none) (hd : st.ns !! d = some .dir) :
    NsWf { st with dfds := <[fd := ⟨d, .idle⟩]> st.dfds } := by
  refine ⟨hw.roots, hw.replay, hw.hist, hw.legacy, fun fd' df' h' => ?_, fun fd' h' => ?_⟩
  · have h'' : (<[fd := (⟨d, .idle⟩ : OsDirFd)]> st.dfds) !! fd' = some df' := h'
    rw [GMap.lookup_insert_eq_iff] at h''
    split at h''
    · cases h''; exact hd
    · exact hw.dfds fd' df' h''
  · show (<[fd := (⟨d, .idle⟩ : OsDirFd)]> st.dfds) !! fd' = none
    rw [GMap.lookup_insert_eq_iff]; split
    · subst_vars; exact absurd hfd h'
    · exact hw.disj fd' h'

/-- ... and the coherence, with the fd's ghost entry. -/
theorem nsCoh_addDirFd {st : OsState} {Γd Γdf} (hc : NsCoh st Γd Γdf) {fd : w64} {d : GoString}
    {g : DirG} {q : Qp} (hg : g = dview Γd.1 Γd.2 d) :
    NsCoh { st with dfds := <[fd := ⟨d, .idle⟩]> st.dfds } Γd (<[fd := (d, .idle g q)]> Γdf) := by
  obtain ⟨h1, h5, h6, h7⟩ := hc
  refine ⟨h1, fun fd' => ?_, fun fd' x df hx hdf => ?_, fun fd' x hx => ?_⟩
  · show ((<[fd := (d, DirPh.idle g q)]> Γdf) !! fd').map (·.1) =
      ((<[fd := (⟨d, .idle⟩ : OsDirFd)]> st.dfds) !! fd').map (·.path)
    rw [GMap.lookup_insert_eq_iff, GMap.lookup_insert_eq_iff]; split
    · rfl
    · exact h5 fd'
  · have hdf' : (<[fd := (⟨d, .idle⟩ : OsDirFd)]> st.dfds) !! fd' = some df := hdf
    rw [GMap.lookup_insert_eq_iff] at hx hdf'
    split at hx
    · rw [if_pos ‹_›] at hdf'; cases hx; cases hdf'; trivial
    · rw [if_neg ‹_›] at hdf'; exact h6 fd' x df hx hdf'
  · rw [GMap.lookup_insert_eq_iff] at hx; split at hx
    · cases hx; exact hg
    · exact h7 fd' x hx

/-- A directory fd's read moved on: the namespace's invariants, with the fd's new ghost phase. -/
theorem nsWfCoh_setRd {st : OsState} {Γd Γdf} (hw : NsWf st) (hc : NsCoh st Γd Γdf) {fd : w64}
    {df : OsDirFd} {x : GoString × DirPh} (hdf : st.dfds !! fd = some df) (hx : Γdf !! fd = some x)
    (rd' : OsDirRead) (ph' : DirPh) (hph : PhOk ph' rd')
    (hrd : ph'.g = dview Γd.1 Γd.2 x.1) :
    NsWf { st with dfds := <[fd := { df with rd := rd' }]> st.dfds } ∧
    NsCoh { st with dfds := <[fd := { df with rd := rd' }]> st.dfds } Γd (<[fd := (x.1, ph')]> Γdf) := by
  have hpath : x.1 = df.path := by have := hc.fds fd; rw [hx, hdf] at this; simpa using this
  refine ⟨⟨hw.roots, hw.replay, hw.hist, hw.legacy, fun fd' df' h' => ?_, fun fd' h' => ?_⟩, ?_⟩
  · have h'' : (<[fd := { df with rd := rd' }]> st.dfds) !! fd' = some df' := h'
    rw [GMap.lookup_insert_eq_iff] at h''; split at h''
    · cases h''; exact hw.dfds fd df hdf
    · exact hw.dfds fd' df' h''
  · show (<[fd := { df with rd := rd' }]> st.dfds) !! fd' = none
    rw [GMap.lookup_insert_eq_iff]; split
    · subst_vars; have := hw.disj _ h'; rw [hdf] at this; cases this
    · exact hw.disj fd' h'
  · obtain ⟨h1, h5, h6, h7⟩ := hc
    refine ⟨h1, fun fd' => ?_, fun fd' x' df' hx' hd' => ?_, fun fd' x' hx' => ?_⟩
    · show ((<[fd := (x.1, ph')]> Γdf) !! fd').map (·.1) =
        ((<[fd := { df with rd := rd' }]> st.dfds) !! fd').map (·.path)
      rw [GMap.lookup_insert_eq_iff, GMap.lookup_insert_eq_iff]; split
      · simp [hpath]
      · exact h5 fd'
    · have hd'' : (<[fd := { df with rd := rd' }]> st.dfds) !! fd' = some df' := hd'
      rw [GMap.lookup_insert_eq_iff] at hx' hd''
      split at hx'
      · rw [if_pos ‹_›] at hd''; cases hx'; cases hd''; exact hph
      · rw [if_neg ‹_›] at hd''; exact h6 fd' x' df' hx' hd''
    · rw [GMap.lookup_insert_eq_iff] at hx'; split at hx'
      · cases hx'; exact hrd
      · exact h7 fd' x' hx'

/-- The names a read begun now sees: the directory's entries. -/
theorem nsPresent_eq {st : OsState} {d : GoString} {g : DirG} (h : entsOf st.ns d = g.now)
    (b : GoString) : nsPresent st d b = (g.now !! b).isSome := by
  rw [← h, entsOf_lookup]
  unfold nsPresent
  by_cases hb : NameOk b <;> simp [hb]

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

theorem nsNewFile_eq : nsNewFile = newFile := rfl

/-- The state after `NsOpen` creates the file `b` of `d` under the fresh key `k` (before its fd). -/
abbrev createdSt (st : OsState) (d b k : GoString) : OsState :=
  (st.nsFree.setFile k nsNewFile).nsDo (.create (child d b) k)

/-- What creating the file `b` of `d` under the fresh key `k` keeps: the files' invariants, with
`k`'s new `OsMeta`; the cells' view; the namespace's invariants, with `d`'s entry pushed. -/
theorem create_facts {st : OsState} {Γb Γm Γf Γt Γd Γdf} {d b k : GoString}
    (hwf : OsWf st) (hcoh : OsCoh st Γb Γm Γf Γt) (hw : NsWf st) (hc : NsCoh st Γd Γdf)
    (hnr : NoDirFds Γdf)
    (hdir : st.ns !! d = some .dir) (hb : NameOk b) (hnone : st.ns !! child d b = none)
    (hk : IsInoKey k) (hkf : k ∉ st.files) :
    OsWf (createdSt st d b k) ∧ OsCoh (createdSt st d b k) Γb (<[k := some newMeta]> Γm) Γf Γt ∧
    cellView (createdSt st d b k) = cellView st ∧
    (∀ q, (createdSt st d b k).size q = st.size q) ∧
    NsWf (createdSt st d b k) ∧
    NsCoh (createdSt st d b k) (Γd.1, Γd.2 ++ [.create (child d b) k]) Γdf ∧
    Γm !! k = none ∧ (createdSt st d b k).file k = some newFile ∧
    (createdSt st d b k).nsBusy = false := by
  have hs0 : FilesSame st st.nsFree := filesSame_nsFree st
  have hkf0 : st.files !! k = none := by
    cases h0 : st.files !! k with
    | none => rfl
    | some x => exact absurd (show (st.files.lookup k).isSome by simp [h0]) hkf
  have hfk : st.nsFree.file k = none := by
    show (st.files !! k).bind id = none; rw [hkf0]; rfl
  have hwf0 := osWf_filesSame hs0 hwf
  have hcoh0 := osCoh_filesSame hs0 hcoh
  have hwfA : OsWf (st.nsFree.setFile k nsNewFile) := osWf_create hwf0 hfk
  have hcohA : OsCoh (st.nsFree.setFile k nsNewFile) Γb (<[k := some newMeta]> Γm) Γf Γt :=
    osCoh_create hwf0 hcoh0 hfk
  have hsB : FilesSame (st.nsFree.setFile k nsNewFile) (createdSt st d b k) := filesSame_nsDo _ _
  have hΓm : Γm !! k = none := (hcoh.meta_dom k).2 hkf0
  -- the namespace
  have hnk : ∀ q, st.ns !! q ≠ some (.file k) := by
    intro q hq
    obtain ⟨-, f, hf⟩ := hw.keys hq
    rw [hkf0] at hf; cases hf
  have hin := fileOpIn_create (k := k) hb hnone
  have hfilesA : ∀ k' f, st.files !! k' = some (some f) →
      ∃ f', (st.nsFree.setFile k nsNewFile).files !! k' = some (some f') := by
    intro k' f hf
    by_cases he : k = k'
    · subst he; rw [hkf0] at hf; cases hf
    · refine ⟨f, ?_⟩
      show (<[k := some nsNewFile]> st.files) !! k' = _
      rw [GMap.lookup_insert_ne _ _ he]; exact hf
  have hwB : NsWf (createdSt st d b k) := by
    refine nsWf_fileOp hw rfl rfl rfl rfl rfl rfl hfilesA (fun k' hk' => ?_)
      (shape_create hw.shape hdir (hw.dir_form hdir) hb hnone hnk) (fun p k' hp => ?_) hin.dir
    · by_cases he : k = k'
      · subst he; exact .inr hk
      · left
        have hk'' : ((<[k := some nsNewFile]> st.files).lookup k').isSome := hk'
        show (st.files.lookup k').isSome
        rwa [show (<[k := some nsNewFile]> st.files).lookup k' = st.files.lookup k' from
          GMap.lookup_insert_ne _ _ he] at hk''
    · have hp' : (<[child d b := OsNode.file k]> st.ns) !! p = some (.file k') := hp
      by_cases he : child d b = p
      · subst he; rw [GMap.lookup_insert] at hp'; cases hp'
        refine ⟨hk, nsNewFile, ?_⟩
        show (<[k := some nsNewFile]> st.files) !! k = _
        rw [GMap.lookup_insert]
      · rw [GMap.lookup_insert_ne _ _ he] at hp'
        obtain ⟨hino, f, hf⟩ := hw.keys hp'
        exact ⟨hino, hfilesA k' f hf⟩
  have hcB : NsCoh (createdSt st d b k) (Γd.1, Γd.2 ++ [.create (child d b) k]) Γdf :=
    nsCoh_log hc hnr rfl rfl rfl
  have hsz : ∀ q, (createdSt st d b k).size q = st.size q := fun q =>
    (sizes_create hfk q).trans rfl
  refine ⟨osWf_filesSame hsB hwfA, osCoh_filesSame hsB hcohA, ?_, hsz, hwB, hcB, hΓm, ?_, rfl⟩
  · rw [cellView_filesSame hsB]
    exact (cellView_create hwf0 hfk).trans (cellView_filesSame hs0)
  · show (<[k := some nsNewFile]> st.files !! k).bind id = some newFile
    rw [GMap.lookup_insert]; rfl

theorem create_tokRes {GF : BundledGFunctors} (hL : OsGS GF) {st : OsState} {d b k : GoString}
    (Γt : GMap Nat TokInfo) (hsz : ∀ q, (createdSt st d b k).size q = st.size q) :
    tokRes hL (createdSt st d b k) Γt = tokRes hL st Γt := by
  unfold tokRes; simp only [affLo_congr hsz]

/-- The worlds of a state, from their resources and facts. -/
theorem worlds_fold {st' : OsState} {Γb Γm Γf Γt} {Γd : NsMap × List NsOp}
    {Γdf : GMap w64 (GoString × DirPh)} {h' : GMap Loc (NonAtomic val)}
    (hwc : OsWf st' ∧ OsCoh st' Γb Γm Γf Γt) (hns : NsWf st' ∧ NsCoh st' Γd Γdf) (bz : Bool)
    (hbz : st'.nsBusy = bz) :
    ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb Γb -∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm Γm -∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γf Γf -∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γt Γt -∗
      tokRes (gooseOsGS (L := L)) st' Γt -∗ cellsRes (GF := GF) (cellView st') -∗ naHeapCtx tls h' -∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γd (histMap Γd) -∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γdf Γdf -∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γz (busyMap bz) -∗
      rdRes (gooseOsGS (L := L)) Γdf -∗
      osWorld (L := L) st' Γb Γm Γf Γt h' ∗ nsWorld (L := L) st' Γd Γdf := by
  iintro HAb HAm HAf HAt Htok Hcells Hσ HAd HAdf HAz Hrd
  unfold osWorld nsWorld
  rw [hbz]
  iframe
  isplitr
  · ipureintro; exact hwc
  · ipureintro; exact hns

/-- `open(2)` of a directory read-only, with a fraction `q` of its view: a new directory fd, not
read, which holds the fraction until its close; or an errno, the fraction back. -/
theorem wp_osNsOpenDir (d : GoString) (q : Qp) (g : DirG) (hE : ↑osN ⊆ E)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osDir (L := L) d (DFrac.own q) g -∗
      (∀ fd : w64, ∀ e : w64, ⌜(e = 0 ∧ 0 ≤ fd.toInt) ∨ (e ≠ 0 ∧ fd = -1)⌝ -∗
        (if e = 0 then osDirFd (L := L) fd (DFrac.own 1) (d, .idle g q)
          else osDir (L := L) d (DFrac.own q) g) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp osFsExt.name "NsOpen" (Val (PairV (#d) (#flRO)))) @ s; E {{ Φ }} := by
  iintro #Hinv Hd HΦ
  iapply wp_os_stepN "NsOpen" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %Γd %Γdf %h Hw Hn
  unfold osWorld nsWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases Hn with ⟨%Hns, HAd, HAdf, HAz, Hrd⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  obtain ⟨hw, hc⟩ := Hns
  icases osDir_view _ _ _ _ $$ HAd Hd with %Hdl
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hdir : st.ns !! d = some .dir := by rw [ns_eq_replay hw hc]; exact Hdl.1.2
  have hnow : entsOf st.ns d = g.now := by rw [Hdl.1.1, dview_now, ← ns_eq_replay hw hc]
  imodintro
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) hwf (filesSame_refl st) Hag
    exact ⟨_, h, st, ⟨d, flRO, rfl, hw.nsPath_dir hdir, flRO_ok, fun h => absurd h (by decide),
      .inr ⟨1, by decide, rfl, .inl rfl⟩⟩, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsOsStep] at Hst
  obtain ⟨p', fl', hv, -, -, -, hres⟩ := Hst
  injection hv with hv1 hv2
  cases go.intoVal_inj hv1; cases go.intoVal_inj hv2
  have hcr : decide ((flRO.toNat / O_CREAT) % 2 = 1) = false := by decide
  have htr : decide ((flRO.toNat / O_TRUNC) % 2 = 1) = false := by decide
  have hacc : flRO.toNat % 4 = O_RDONLY := by decide
  simp only [hcr, htr, hacc, Bool.false_eq_true, ↓reduceIte] at hres
  rcases hres with ⟨st1, tgt, fd, heff, hfree, hst, rfl⟩ | ⟨e, he, rfl, hst⟩
  · unfold NsOpenEffect at heff
    rw [hdir] at heff
    obtain ⟨-, -, -, hst1, rfl⟩ := heff
    subst st1
    obtain ⟨hfd0, hfdn, hdfn⟩ := hfree
    have hΓ : Γdf !! fd = none := by
      have := hc.fds fd; rw [hdfn] at this
      cases h0 : Γdf !! fd with
      | none => rfl
      | some x => rw [h0] at this; cases this
    imod gAuth_insert _ _ _ fd (d, DirPh.idle g q) hΓ $$ HAdf with ⟨HAdf, Hfd⟩
    have hs : FilesSame st st' := by rw [hst]; exact ⟨rfl, rfl, rfl, rfl⟩
    have hw' : NsWf st' := by rw [hst]; exact nsWf_addDirFd hw hfdn hdir
    have hc' : NsCoh st' Γd (<[fd := (d, DirPh.idle g q)]> Γdf) := by
      rw [hst]; exact nsCoh_addDirFd hc Hdl.1.1
    ihave Hrd : rdRes (gooseOsGS (L := L)) (<[fd := (d, DirPh.idle g q)]> Γdf) $$ [Hrd Hd]
    · unfold rdRes
      iapply (BigSepM.bigSepM_insert (M := GMap w64)
        (Φ := fun (_ : w64) (x : GoString × DirPh) => rdPart (gooseOsGS (L := L)) x) hΓ).2
      iframe Hrd; unfold rdPart osDir osNsAll; dsimp only [DirPh.q, DirPh.g]; iexact Hd
    imod ns_step_close hwf hcoh hs Hr Hfr hw' hc' st.nsBusy (by rw [hst]) $$ HAb HAm HAf HAt Htok
      Hcells Hσ HAd HAdf HAz Hrd with ⟨Hw, Hn⟩
    imodintro
    iexists Γb, Γm, Γf, Γt, Γd, (<[fd := (d, DirPh.idle g q)]> Γdf)
    unfold osWorld nsWorld rdRes
    iframe Hw Hn
    iapply wp_value'
    iapply HΦ $$ %fd %0 %(.inl ⟨rfl, hfd0⟩)
    rw [if_pos rfl]; unfold osDirFd; iexact Hfd
  · have hst' : st' = st := by
      rcases hst with rfl | ⟨tgt, heff⟩
      · rfl
      · unfold NsOpenEffect at heff; rw [hdir] at heff; exact heff.2.2.2.1
    subst hst'
    imod ns_step_close hwf hcoh (filesSame_refl st') Hr Hfr hw hc st'.nsBusy rfl $$ HAb HAm HAf
      HAt Htok Hcells Hσ HAd HAdf HAz Hrd with ⟨Hw, Hn⟩
    imodintro
    iexists Γb, Γm, Γf, Γt, Γd, Γdf
    unfold osWorld nsWorld
    iframe Hw Hn
    iapply wp_value'
    iapply HΦ $$ %(-1) %e %(.inr ⟨he, rfl⟩)
    rw [if_neg he]; iexact Hd

/-- `open(2)` read-only of the file `b` of `d` (of key `k`), with a fraction of `k`'s `OsMeta`:
the file exists (`mo ≠ none`); a new fd on `k`, or an errno. -/
theorem wp_osNsOpenFile (d b k : GoString) (dq : DFrac) (g : DirG) (hb : NameOk b)
    (hf : g.now !! b = some (.file k)) (dqm : DFrac) (mo : Option OsMeta) (hE : ↑osN ⊆ E)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osDir (L := L) d dq g -∗ osMeta (L := L) k dqm mo -∗
      (∀ fd : w64, ∀ e : w64, ⌜mo ≠ none⌝ -∗ ⌜(e = 0 ∧ 0 ≤ fd.toInt) ∨ (e ≠ 0 ∧ fd = -1)⌝ -∗
        osDir (L := L) d dq g -∗ osMeta (L := L) k dqm mo -∗
        (if e = 0 then osFd (L := L) fd (DFrac.own 1) ⟨k, true, false⟩ else emp) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp osFsExt.name "NsOpen" (Val (PairV (#(child d b)) (#flRO)))) @ s; E
        {{ Φ }} := by
  iintro #Hinv Hd Hm HΦ
  iapply wp_os_stepN "NsOpen" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %Γd %Γdf %h Hw Hn
  unfold osWorld nsWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases Hn with ⟨%Hns, HAd, HAdf, HAz, Hrd⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  obtain ⟨hw, hc⟩ := Hns
  unfold osMeta
  icases osDir_view _ _ _ _ $$ HAd Hd with %Hdl
  icases gAuth_lookup _ _ _ _ _ _ $$ HAm Hm with %Hml
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hdir : st.ns !! d = some .dir := by rw [ns_eq_replay hw hc]; exact Hdl.1.2
  have hnow : entsOf st.ns d = g.now := by rw [Hdl.1.1, dview_now, ← ns_eq_replay hw hc]
  have hfile : st.ns !! child d b = some (.file k) := by
    rw [← entsOf_child st.ns d b hb, hnow]; exact hf
  obtain ⟨-, f, hkf⟩ := hw.keys hfile
  have hmo : mo ≠ none := by
    rintro rfl
    have := (hcoh.meta_none k).1 Hml; rw [hkf] at this; cases this
  have hfk : st.file k = some f := file_eq_some.2 hkf
  imodintro
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) hwf (filesSame_refl st) Hag
    exact ⟨_, h, st, ⟨child d b, flRO, rfl, .inr (hw.nsName_child hdir hb), flRO_ok,
      fun h => absurd h (by decide), .inr ⟨1, by decide, rfl, .inl rfl⟩⟩, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsOsStep] at Hst
  obtain ⟨p', fl', hv, -, -, -, hres⟩ := Hst
  injection hv with hv1 hv2
  cases go.intoVal_inj hv1; cases go.intoVal_inj hv2
  have hcr : decide ((flRO.toNat / O_CREAT) % 2 = 1) = false := by decide
  have htr : decide ((flRO.toNat / O_TRUNC) % 2 = 1) = false := by decide
  have hacc : flRO.toNat % 4 = O_RDONLY := by decide
  simp only [hcr, htr, hacc, Bool.false_eq_true, ↓reduceIte] at hres
  rcases hres with ⟨st1, tgt, fd, heff, hfree, hst, rfl⟩ | ⟨e, he, rfl, hst⟩
  · unfold NsOpenEffect at heff
    rw [hfile] at heff
    obtain ⟨⟨f', -, hst1⟩, rfl⟩ := heff
    simp only [Bool.false_eq_true, ↓reduceIte] at hst1
    subst st1
    obtain ⟨hfd0, hfdn, hdfn⟩ := hfree
    have hfdo : (⟨k, decide (O_RDONLY ≠ O_WRONLY), decide (O_RDONLY ≠ O_RDONLY)⟩ : OsFd) =
        ⟨k, true, false⟩ := by simp [O_RDONLY, O_WRONLY]
    simp only at hst
    have hΓf : Γf !! fd = none := by rw [hcoh.fds]; exact hfdn
    imod gAuth_insert _ _ _ fd (⟨k, true, false⟩ : OsFd) hΓf $$ HAf with ⟨HAf, Hfd⟩
    have hst' : st' = { st with fds := <[fd := ⟨k, true, false⟩]> st.fds } := by
      rw [hst]; congr 2
    subst hst'
    have hwf' := osWf_addFd hwf fd ⟨k, true, false⟩ ⟨f, hfk⟩
    have hcv : cellView { st with fds := <[fd := ⟨k, true, false⟩]> st.fds } = cellView st :=
      cellView_congr rfl rfl rfl
    imod cells_same hwf hwf' Hr Hfr rfl hcv $$ [Hσ Hcells] with ⟨Hσ, Hcells⟩
    · iframe
    have htr' : tokRes (gooseOsGS (L := L)) { st with fds := <[fd := ⟨k, true, false⟩]> st.fds } Γt =
        tokRes (gooseOsGS (L := L)) st Γt := rfl
    have hw' : NsWf { st with fds := <[fd := ⟨k, true, false⟩]> st.fds } := by
      refine ⟨hw.roots, hw.replay, hw.hist, hw.legacy, hw.dfds, fun fd' h' => ?_⟩
      show st.dfds !! fd' = none
      by_cases he : fd = fd'
      · subst he; exact hdfn
      · apply hw.disj fd'
        have h'' : (<[fd := (⟨k, true, false⟩ : OsFd)]> st.fds) !! fd' ≠ none := h'
        rwa [GMap.lookup_insert_ne _ _ he] at h''
    imodintro
    iexists Γb, Γm, (<[fd := ⟨k, true, false⟩]> Γf), Γt, Γd, Γdf
    rw [htr']
    iframe
    isplitr
    · ipureintro
      refine ⟨hwf', ?_⟩
      rw [hcoh.fds]; exact osCoh_fds hcoh _
    isplitr
    · ipureintro; exact ⟨hw', hc.congr rfl rfl rfl⟩
    iapply wp_value'
    iapply HΦ $$ %fd %0 %hmo %(.inl ⟨rfl, hfd0⟩) Hd Hm
    rw [if_pos rfl]; unfold osFd; iexact Hfd
  · have hst' : st' = st := by
      rcases hst with rfl | ⟨tgt, heff⟩
      · rfl
      · unfold NsOpenEffect at heff; rw [hfile] at heff
        obtain ⟨⟨f', -, h1⟩, -⟩ := heff
        simpa using h1
    subst hst'
    imod ns_step_close hwf hcoh (filesSame_refl st') Hr Hfr hw hc st'.nsBusy rfl $$ HAb HAm HAf
      HAt Htok Hcells Hσ HAd HAdf HAz Hrd with ⟨Hw, Hn⟩
    imodintro
    iexists Γb, Γm, Γf, Γt, Γd, Γdf
    unfold osWorld nsWorld
    iframe Hw Hn
    iapply wp_value'
    iapply HΦ $$ %(-1) %e %hmo %(.inr ⟨he, rfl⟩) Hd Hm
    rw [if_neg he]; iempintro

/-- `open(2)` with `O_RDWR | O_CREAT` of a new name `b` of `d`, with `d`'s whole ghost entry and the
in-flight flag set: the flag cleared; on success a new file under a fresh key `k`, `b` pushed in
`d`'s entry, `k`'s `OsMeta` whole and an fd on it; on failure the file may have been created. -/
theorem wp_osNsOpenCreate (d b : GoString) (g : DirG) (hb : NameOk b) (hn : g.now !! b = none)
    (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osDir (L := L) d (DFrac.own 1) g -∗ osNsBusy (L := L) true -∗
      (∀ fd : w64, ∀ e : w64, osNsBusy (L := L) false -∗
        ((⌜e = 0 ∧ 0 ≤ fd.toInt⌝ ∗ ∃ k, ⌜IsInoKey k⌝ ∗
            osDir (L := L) d (DFrac.own 1) (g.push (.put b (.file k))) ∗
            osMeta (L := L) k (DFrac.own 1) (some newMeta) ∗
            osFd (L := L) fd (DFrac.own 1) ⟨k, true, true⟩) ∨
         (⌜e ≠ 0 ∧ fd = -1⌝ ∗ (osDir (L := L) d (DFrac.own 1) g ∨ ∃ k, ⌜IsInoKey k⌝ ∗
            osDir (L := L) d (DFrac.own 1) (g.push (.put b (.file k))) ∗
            osMeta (L := L) k (DFrac.own 1) (some newMeta)))) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp osFsExt.name "NsOpen" (Val (PairV (#(child d b)) (#flCreat)))) @ s; E
        {{ Φ }} := by
  iintro #Hinv Hd Hz HΦ
  iapply wp_os_stepN "NsOpen" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %Γd %Γdf %h Hw Hn
  unfold osWorld nsWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases Hn with ⟨%Hns, HAd, HAdf, HAz, Hrd⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  obtain ⟨hw, hc⟩ := Hns
  icases rdRes_whole d g Γdf $$ Hd Hrd with ⟨%Hnr, Hd, Hrd⟩
  unfold osNsBusy
  icases osDir_view _ _ _ _ $$ HAd Hd with %Hdl
  icases gAuth_lookup _ _ _ _ _ _ $$ HAz Hz with %Hzl
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hb1 : st.nsBusy = true := by
    simp only [busyMap, GMap.lookup_singleton_eq, Option.some.injEq] at Hzl; exact Hzl
  have hdir : st.ns !! d = some .dir := by rw [ns_eq_replay hw hc]; exact Hdl.1.2
  have hnow : entsOf st.ns d = g.now := by rw [Hdl.1.1, dview_now, ← ns_eq_replay hw hc]
  have hnone : st.ns !! child d b = none := by
    rw [← entsOf_child st.ns d b hb, hnow]; exact hn
  have hcr : decide ((flCreat.toNat / O_CREAT) % 2 = 1) = true := by decide
  have htr : decide ((flCreat.toNat / O_TRUNC) % 2 = 1) = false := by decide
  have hacc : flCreat.toNat % 4 = 2 := by decide
  have hs0 : FilesSame st st.nsFree := filesSame_nsFree st
  imodintro
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) hwf hs0 Hag
    refine ⟨_, h, st.nsFree, ⟨child d b, flCreat, rfl, .inr (hw.nsName_child hdir hb), flCreat_ok,
      fun _ => hb1, .inr ⟨1, by decide, rfl, .inl ?_⟩⟩, hfr, hr⟩
    simp only [hcr, ↓reduceIte]
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsOsStep] at Hst
  obtain ⟨p', fl', hv, -, -, -, hres⟩ := Hst
  injection hv with hv1 hv2
  cases go.intoVal_inj hv1; cases go.intoVal_inj hv2
  simp only [hcr, htr, hacc, ↓reduceIte] at hres
  imod gAuth_update _ _ _ _ _ false $$ HAz Hz with ⟨HAz, Hz⟩
  rw [busyMap_insert]
  -- what an effect is: a file created under a fresh key
  have heffect : ∀ st1 tgt, NsOpenEffect st.nsFree (child d b) 2 true false st1 tgt →
      ∃ k, IsInoKey k ∧ k ∉ st.files ∧ st1 = createdSt st d b k ∧ tgt = some k := by
    intro st1 tgt heff
    unfold NsOpenEffect at heff
    rw [show st.nsFree.ns = st.ns from rfl, hnone] at heff
    obtain ⟨-, -, -, k, hk, hkf, rfl, rfl⟩ := heff
    exact ⟨k, hk, hkf, rfl, rfl⟩
  -- the ghost state of a creation
  have hghost : ∀ k, IsInoKey k → k ∉ st.files →
      ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm Γm -∗
        gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γd (histMap Γd) -∗
        osDir (L := L) d (DFrac.own 1) g ==∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm (<[k := some newMeta]> Γm) ∗
        gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γd
          (histMap (Γd.1, Γd.2 ++ [.create (child d b) k])) ∗
        osDir (L := L) d (DFrac.own 1) (g.push (.put b (.file k))) ∗
        osMeta (L := L) k (DFrac.own 1) (some newMeta) := by
    intro k hk hkf
    obtain ⟨-, -, -, -, -, -, hΓm, -, -⟩ :=
      create_facts hwf hcoh hw hc Hnr hdir hb hnone hk hkf
    iintro HAm HAd Hd
    imod gAuth_insert _ _ _ k (some newMeta) hΓm $$ HAm with ⟨HAm, Hm⟩
    imod osDir_update Γd (Γd.1, Γd.2 ++ [.create (child d b) k]) d g (g.push (.put b (.file k)))
      ⟨by rw [Hdl.1.1]; exact (dview_create _ _ d b k hb).symm,
       AllDir.snoc Hdl.2 (apply_child_dir Hdl.1.2 _ (.inl ⟨b, k, hb, rfl⟩))⟩ $$ HAd Hd with ⟨HAd, Hd⟩
    imodintro
    unfold osMeta
    iframe
  rcases hres with ⟨st1, tgt, fd, heff, hfree, hst, rfl⟩ | ⟨e, he, rfl, hst | ⟨tgt, heff⟩⟩
  · -- success
    obtain ⟨k, hk, hkf, rfl, rfl⟩ := heffect st1 tgt heff
    obtain ⟨hwfB, hcohB, hcvB, hszB, hwB, hcB, -, hfkB, hbB⟩ :=
      create_facts hwf hcoh hw hc Hnr hdir hb hnone hk hkf
    obtain ⟨hfd0, hfdn, hdfn⟩ := hfree
    have hfdB : (createdSt st d b k).fds !! fd = none := hfdn
    have hst' : st' = { createdSt st d b k with
        fds := <[fd := ⟨k, true, true⟩]> (createdSt st d b k).fds } := by
      rw [hst]; simp [O_WRONLY, O_RDONLY]
    subst hst'
    imod hghost k hk hkf $$ HAm HAd Hd with ⟨HAm, HAd, Hd, Hm⟩
    have hΓf : Γf !! fd = none := by rw [hcoh.fds]; exact hfdn
    imod gAuth_insert _ _ _ fd (⟨k, true, true⟩ : OsFd) hΓf $$ HAf with ⟨HAf, Hfd⟩
    have hwf' := osWf_addFd hwfB fd ⟨k, true, true⟩ ⟨_, hfkB⟩
    have hcv : cellView { createdSt st d b k with
        fds := <[fd := ⟨k, true, true⟩]> (createdSt st d b k).fds } = cellView st :=
      (cellView_congr rfl rfl rfl).trans hcvB
    imod cells_same hwf hwf' Hr Hfr rfl hcv $$ [Hσ Hcells] with ⟨Hσ, Hcells⟩
    · iframe
    have htr' : tokRes (gooseOsGS (L := L)) { createdSt st d b k with
        fds := <[fd := ⟨k, true, true⟩]> (createdSt st d b k).fds } Γt =
        tokRes (gooseOsGS (L := L)) st Γt := create_tokRes _ Γt hszB
    have hw' : NsWf { createdSt st d b k with
        fds := <[fd := ⟨k, true, true⟩]> (createdSt st d b k).fds } := by
      refine ⟨hwB.roots, hwB.replay, hwB.hist, hwB.legacy, hwB.dfds, fun fd' h' => ?_⟩
      show (createdSt st d b k).dfds !! fd' = none
      by_cases he : fd = fd'
      · subst he
        rw [show (createdSt st d b k).dfds = GMap.fmap (·.note (.create (child d b) k)) st.dfds
          from rfl, GMap.lookup_fmap, hdfn]; rfl
      · apply hwB.disj fd'
        have h'' : (<[fd := (⟨k, true, true⟩ : OsFd)]> (createdSt st d b k).fds) !! fd' ≠ none := h'
        rwa [GMap.lookup_insert_ne _ _ he] at h''
    ihave Htok : tokRes (gooseOsGS (L := L)) { createdSt st d b k with
        fds := <[fd := ⟨k, true, true⟩]> (createdSt st d b k).fds } Γt $$ [Htok]
    · rw [htr']; iexact Htok
    have hcoh' : OsCoh { createdSt st d b k with
        fds := <[fd := ⟨k, true, true⟩]> (createdSt st d b k).fds } Γb (<[k := some newMeta]> Γm)
        (<[fd := ⟨k, true, true⟩]> Γf) Γt := by
      have : Γf = (createdSt st d b k).fds := by rw [hcoh.fds]; rfl
      rw [this]; exact osCoh_fds hcohB _
    ihave Hwn := worlds_fold ⟨hwf', hcoh'⟩ ⟨hw', hcB.congr rfl rfl rfl⟩ false hbB
      $$ HAb HAm HAf HAt Htok Hcells Hσ HAd HAdf HAz Hrd
    icases Hwn with ⟨Hw, Hn⟩
    imodintro
    iexists Γb, (<[k := some newMeta]> Γm), (<[fd := ⟨k, true, true⟩]> Γf), Γt,
      (Γd.1, Γd.2 ++ [.create (child d b) k]), Γdf
    unfold osWorld nsWorld
    iframe Hw Hn
    iapply wp_value'
    iapply HΦ $$ %fd %0 Hz
    ileft
    isplitr
    · ipureintro; exact ⟨rfl, hfd0⟩
    iexists k
    isplitr
    · ipureintro; exact hk
    unfold osMeta osFd
    iframe Hd Hm
    iexact Hfd
  · -- failure, no effect
    subst hst
    imod ns_step_close hwf hcoh hs0 Hr Hfr (nsWf_nsFree hw) (nsCoh_nsFree hc) false rfl $$ HAb HAm
      HAf HAt Htok Hcells Hσ HAd HAdf HAz Hrd with ⟨Hw, Hn⟩
    imodintro
    iexists Γb, Γm, Γf, Γt, Γd, Γdf
    unfold osWorld nsWorld
    iframe Hw Hn
    iapply wp_value'
    iapply HΦ $$ %(-1) %e Hz
    iright
    isplitr
    · ipureintro; exact ⟨he, rfl⟩
    ileft; iexact Hd
  · -- failure, created
    obtain ⟨k, hk, hkf, rfl, -⟩ := heffect st' tgt heff
    obtain ⟨hwfB, hcohB, hcvB, hszB, hwB, hcB, -, -, hbB⟩ :=
      create_facts hwf hcoh hw hc Hnr hdir hb hnone hk hkf
    imod hghost k hk hkf $$ HAm HAd Hd with ⟨HAm, HAd, Hd, Hm⟩
    imod cells_same hwf hwfB Hr Hfr rfl hcvB $$ [Hσ Hcells] with ⟨Hσ, Hcells⟩
    · iframe
    ihave Htok : tokRes (gooseOsGS (L := L)) (createdSt st d b k) Γt $$ [Htok]
    · rw [create_tokRes _ Γt hszB]; iexact Htok
    ihave Hwn := worlds_fold ⟨hwfB, hcohB⟩ ⟨hwB, hcB⟩ false hbB
      $$ HAb HAm HAf HAt Htok Hcells Hσ HAd HAdf HAz Hrd
    icases Hwn with ⟨Hw, Hn⟩
    imodintro
    iexists Γb, (<[k := some newMeta]> Γm), Γf, Γt, (Γd.1, Γd.2 ++ [.create (child d b) k]), Γdf
    unfold osWorld nsWorld
    iframe Hw Hn
    iapply wp_value'
    iapply HΦ $$ %(-1) %e Hz
    iright
    isplitr
    · ipureintro; exact ⟨he, rfl⟩
    iright
    iexists k
    isplitr
    · ipureintro; exact hk
    unfold osMeta
    iframe

theorem phOk_idle {g : DirG} {q : Qp} {rd : OsDirRead} (h : PhOk (.idle g q) rd) : rd = .idle := by
  cases rd <;> simp_all [PhOk]

theorem phOk_reading {rs : List GoString} {g : DirG} {q : Qp} {rd : OsDirRead}
    (h : PhOk (.reading rs g q) rd) : ∃ u s r, rd = .reading u s r ∧
      ∀ b, u b = (g.now !! b).isSome ∧ s b = (g.now !! b).isSome ∧ r b = decide (b ∈ rs) := by
  cases rd with
  | reading u s r => exact ⟨u, s, r, rfl, h⟩
  | _ => simp [PhOk] at h

/-- The values of a step of `Readdirnames`: a name, the end, an errno. -/
abbrev rdName (b : GoString) : val := PairV (#b) (PairV (#(0 : w64)) (#(0 : w64)))
abbrev rdEnd : val := PairV (#([] : GoString)) (PairV (#(1 : w64)) (#(0 : w64)))
abbrev rdErr (e : w64) : val := PairV (#([] : GoString)) (PairV (#(0 : w64)) (#e))

/-- One step of a read of a directory fd, its read begun (`rs` the names returned) or about to be
(`fresh`); the fd holds a fraction `q` of the history, of which `g` is the directory's view: a
name of the directory not returned, the end once all were, or an errno. -/
theorem wp_osDirReadStep (fd : w64) (d : GoString) (rs : List GoString) (g : DirG) (q : Qp)
    (fresh : Bool) (hfr : fresh = true → rs = []) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗
      osDirFd (L := L) fd (DFrac.own 1) (d, if fresh then .idle g q else .reading rs g q) -∗
      (∀ v, ((∃ b, ⌜v = rdName b ∧ (g.now !! b).isSome ∧ b ∉ rs⌝ ∗
              osDirFd (L := L) fd (DFrac.own 1) (d, .reading (b :: rs) g q)) ∨
            (⌜v = rdEnd ∧ ∀ b, (g.now !! b).isSome → b ∈ rs⌝ ∗
              osDirFd (L := L) fd (DFrac.own 1) (d, .done g q)) ∨
            (∃ e : w64, ⌜e ≠ 0 ∧ v = rdErr e⌝ ∗
              osDirFd (L := L) fd (DFrac.own 1) (d, .reading rs g q))) -∗ Φ v) -∗
      WP (ExternalOp osFsExt.name "DirReadNext" (Val (#fd))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd HΦ
  iapply wp_os_stepN "DirReadNext" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %Γd %Γdf %h Hw Hn
  unfold osWorld nsWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases Hn with ⟨%Hns, HAd, HAdf, HAz, Hrd⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  obtain ⟨hw, hc⟩ := Hns
  unfold osDirFd
  icases gAuth_lookup _ _ _ _ _ _ $$ HAdf Hfd with %Hfl
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  obtain ⟨df, hdf⟩ : ∃ df, st.dfds !! fd = some df := by
    have := hc.fds fd; rw [Hfl] at this
    cases h0 : st.dfds !! fd with
    | none => rw [h0] at this; cases this
    | some df => exact ⟨df, rfl⟩
  have hpath : df.path = d := by have := hc.fds fd; rw [Hfl, hdf] at this; simpa using this.symm
  have hph := hc.ph fd _ df Hfl hdf
  -- the directory's ghost entry, and the read's state
  have hgd : g = dview Γd.1 Γd.2 d → entsOf st.ns d = g.now := fun h => by
    rw [h, dview_now, ← ns_eq_replay hw hc]
  have Hdl : g = dview Γd.1 Γd.2 d := by
    have := hc.rd fd _ Hfl; cases fresh <;> exact this
  have hcur : ∃ u s r,
      df.rd.cur st df.path = some (u, s, r) ∧
      ∀ b, u b = (g.now !! b).isSome ∧ s b = (g.now !! b).isSome ∧ r b = decide (b ∈ rs) := by
    cases fresh with
    | true =>
      have hrd := phOk_idle hph
      have hents := hgd Hdl
      refine ⟨nsPresent st d, nsPresent st d, fun _ => false, by rw [hrd, hpath]; rfl,
        fun b => ⟨nsPresent_eq hents b, nsPresent_eq hents b, ?_⟩⟩
      rw [hfr rfl]; simp
    | false =>
      obtain ⟨u, s, r, hrd, hus⟩ := phOk_reading hph
      exact ⟨u, s, r, by rw [hrd]; rfl, hus⟩
  obtain ⟨u, s, r, hcur', hus⟩ := hcur
  have hents := hgd Hdl
  have hs : ∀ rd', FilesSame st { st with dfds := <[fd := { df with rd := rd' }]> st.dfds } :=
    fun _ => ⟨rfl, rfl, rfl, rfl⟩
  imodintro
  isplitr
  · ipureintro
    obtain ⟨hfr', hr⟩ := step_filesSame (h := h) hwf (hs (.reading u s r)) Hag
    exact ⟨_, h, _, ⟨fd, df, u, s, r, rfl, hdf, hcur', .inr (.inr ⟨1, by decide, rfl, rfl⟩)⟩,
      hfr', hr⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr', Hr⟩ := Hst
  simp only [IsOsStep] at Hst
  obtain ⟨fd', df', u', s', r', hv, hdf', hcur'', hres⟩ := Hst
  cases go.intoVal_inj hv
  rw [hdf] at hdf'; cases hdf'
  rw [hcur'] at hcur''; cases hcur''
  -- the reads' fractions, with the fd's entry swapped
  unfold rdRes
  icases (BigSepM.bigSepM_insert_acc (M := GMap w64)
    (Φ := fun (_ : w64) (x : GoString × DirPh) => rdPart (gooseOsGS (L := L)) x) Hfl) $$ Hrd
    with ⟨Hx, Hrd⟩
  ihave Hq : iprop(∃ V : NsMap × List NsOp, gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γd ()
      (DFrac.own q) V ∗ ⌜g = dview V.1 V.2 d ∧ AllDir V d⌝) $$ [Hx]
  · unfold rdPart
    cases fresh <;> (simp only [Bool.false_eq_true, ↓reduceIte, DirPh.q, DirPh.g] at *; iexact Hx)
  -- the fd's ghost entry, to the new phase
  have hfinish : ∀ (rd' : OsDirRead) (ph' : DirPh), PhOk ph' rd' →
      ph'.g = dview Γd.1 Γd.2 d →
      st' = { st with dfds := <[fd := { df with rd := rd' }]> st.dfds } →
      ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb Γb -∗
        gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm Γm -∗
        gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γf Γf -∗
        gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γt Γt -∗
        tokRes (gooseOsGS (L := L)) st Γt -∗ cellsRes (GF := GF) (cellView st) -∗ naHeapCtx tls h -∗
        gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γd (histMap Γd) -∗
        gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γdf Γdf -∗
        gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γdf fd (DFrac.own 1)
          (d, if fresh then DirPh.idle g q else .reading rs g q) -∗
        gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γz (busyMap st.nsBusy) -∗
        ([∗map] k ↦ v ∈ <[fd := (d, ph')]> Γdf, rdPart (gooseOsGS (L := L)) v) ==∗
        osWorld (L := L) st' Γb Γm Γf Γt h' ∗ nsWorld (L := L) st' Γd (<[fd := (d, ph')]> Γdf) ∗
        osDirFd (L := L) fd (DFrac.own 1) (d, ph') := by
    intro rd' ph' hok hrd hst
    subst hst
    obtain ⟨hw', hc'⟩ := nsWfCoh_setRd hw hc hdf Hfl rd' ph' hok hrd
    iintro HAb HAm HAf HAt Htok Hcells Hσ HAd HAdf Hfd HAz Hrd
    imod gAuth_update _ _ _ _ _ (d, ph') $$ HAdf Hfd with ⟨HAdf, Hfd⟩
    imod ns_step_close hwf hcoh (hs rd') Hr Hfr' hw' hc' st.nsBusy rfl $$ HAb HAm HAf HAt Htok
      Hcells Hσ HAd HAdf HAz [Hrd] with ⟨Hw, Hn⟩
    · unfold rdRes; iexact Hrd
    imodintro
    iframe Hw Hn
    unfold osDirFd; iexact Hfd
  rcases hres with ⟨b, hsb, hrb, hst, rfl⟩ | ⟨hall, hst, rfl⟩ | ⟨e, he, hst, rfl⟩
  · -- a name
    have hb : (g.now !! b).isSome := by rw [← (hus b).2.1]; exact hsb
    have hbr : b ∉ rs := by
      intro hm; have := (hus b).2.2; rw [hrb] at this; simp [hm] at this
    have hok : PhOk (.reading (b :: rs) g q) (.reading u s (fun x => r x || decide (x = b))) := by
      intro x
      refine ⟨(hus x).1, (hus x).2.1, ?_⟩
      show (r x || decide (x = b)) = _
      rw [(hus x).2.2]; by_cases hx : x = b <;> simp [hx]
    ihave Hrd := Hrd $$ %(d, .reading (b :: rs) g q) [Hq]
    · unfold rdPart; dsimp only [DirPh.q, DirPh.g]; iexact Hq
    imod hfinish _ _ hok Hdl hst $$ HAb HAm HAf HAt Htok
      Hcells Hσ HAd HAdf Hfd HAz Hrd with ⟨Hw, Hn, Hfd⟩
    imodintro
    iexists Γb, Γm, Γf, Γt, Γd, (<[fd := (d, .reading (b :: rs) g q)]> Γdf)
    unfold osWorld nsWorld rdRes
    iframe Hw Hn
    iapply wp_value'
    iapply HΦ
    unfold osDirFd; ileft; iexists b; iframe Hfd; ipureintro; exact ⟨rfl, hb, hbr⟩
  · -- the end: every name returned
    have hall' : ∀ b, (g.now !! b).isSome → b ∈ rs := by
      intro b hb
      have := hall b (by rw [(hus b).1]; exact hb) (by rw [nsPresent_eq (hpath ▸ hents) b]; exact hb)
      rw [(hus b).2.2] at this; simpa using this
    ihave Hrd := Hrd $$ %(d, DirPh.done g q) [Hq]
    · unfold rdPart; dsimp only [DirPh.q, DirPh.g]; iexact Hq
    imod hfinish _ _ (by trivial : PhOk (.done g q) .done) Hdl hst $$ HAb HAm HAf
      HAt Htok Hcells Hσ HAd HAdf Hfd HAz Hrd with ⟨Hw, Hn, Hfd⟩
    imodintro
    iexists Γb, Γm, Γf, Γt, Γd, (<[fd := (d, .done g q)]> Γdf)
    unfold osWorld nsWorld rdRes
    iframe Hw Hn
    iapply wp_value'
    iapply HΦ
    unfold osDirFd; iright; ileft; iframe Hfd; ipureintro; exact ⟨rfl, hall'⟩
  · -- an errno: the read begun, nothing returned
    have hok : PhOk (.reading rs g q) (.reading u s r) := fun x => hus x
    ihave Hrd := Hrd $$ %(d, .reading rs g q) [Hq]
    · unfold rdPart; dsimp only [DirPh.q, DirPh.g]; iexact Hq
    imod hfinish _ _ hok Hdl hst $$ HAb HAm HAf HAt Htok
      Hcells Hσ HAd HAdf Hfd HAz Hrd with ⟨Hw, Hn, Hfd⟩
    imodintro
    iexists Γb, Γm, Γf, Γt, Γd, (<[fd := (d, .reading rs g q)]> Γdf)
    unfold osWorld nsWorld rdRes
    iframe Hw Hn
    iapply wp_value'
    iapply HΦ
    unfold osDirFd; iright; iright; iexists e; iframe Hfd; ipureintro; exact ⟨he, rfl⟩

/-- `open(2)` with `O_RDWR | O_CREAT` of the existing file `b` of `d` (of key `k`), with the
in-flight flag set and a fraction of `k`'s `OsMeta`: the flag cleared; a new fd on `k`, or an
errno. -/
theorem wp_osNsOpenCreatExisting (d b k : GoString) (dq : DFrac) (g : DirG) (hb : NameOk b)
    (hf : g.now !! b = some (.file k)) (dqm : DFrac) (mo : Option OsMeta) (hE : ↑osN ⊆ E)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osDir (L := L) d dq g -∗ osMeta (L := L) k dqm mo -∗
      osNsBusy (L := L) true -∗
      (∀ fd : w64, ∀ e : w64, ⌜mo ≠ none⌝ -∗ ⌜(e = 0 ∧ 0 ≤ fd.toInt) ∨ (e ≠ 0 ∧ fd = -1)⌝ -∗
        osDir (L := L) d dq g -∗ osMeta (L := L) k dqm mo -∗ osNsBusy (L := L) false -∗
        (if e = 0 then osFd (L := L) fd (DFrac.own 1) ⟨k, true, true⟩ else emp) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp osFsExt.name "NsOpen" (Val (PairV (#(child d b)) (#flCreat)))) @ s; E
        {{ Φ }} := by
  iintro #Hinv Hd Hm Hz HΦ
  iapply wp_os_stepN "NsOpen" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %Γd %Γdf %h Hw Hn
  unfold osWorld nsWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases Hn with ⟨%Hns, HAd, HAdf, HAz, Hrd⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  obtain ⟨hw, hc⟩ := Hns
  unfold osMeta osNsBusy
  icases osDir_view _ _ _ _ $$ HAd Hd with %Hdl
  icases gAuth_lookup _ _ _ _ _ _ $$ HAm Hm with %Hml
  icases gAuth_lookup _ _ _ _ _ _ $$ HAz Hz with %Hzl
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hb1 : st.nsBusy = true := by
    simp only [busyMap, GMap.lookup_singleton_eq, Option.some.injEq] at Hzl; exact Hzl
  have hdir : st.ns !! d = some .dir := by rw [ns_eq_replay hw hc]; exact Hdl.1.2
  have hnow : entsOf st.ns d = g.now := by rw [Hdl.1.1, dview_now, ← ns_eq_replay hw hc]
  have hfile : st.ns !! child d b = some (.file k) := by
    rw [← entsOf_child st.ns d b hb, hnow]; exact hf
  obtain ⟨-, f, hkf⟩ := hw.keys hfile
  have hmo : mo ≠ none := by
    rintro rfl
    have := (hcoh.meta_none k).1 Hml; rw [hkf] at this; cases this
  have hfk : st.nsFree.file k = some f := file_eq_some.2 hkf
  have hcr : decide ((flCreat.toNat / O_CREAT) % 2 = 1) = true := by decide
  have htr : decide ((flCreat.toNat / O_TRUNC) % 2 = 1) = false := by decide
  have hacc : flCreat.toNat % 4 = 2 := by decide
  imodintro
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) hwf (filesSame_nsFree st) Hag
    refine ⟨_, h, st.nsFree, ⟨child d b, flCreat, rfl, .inr (hw.nsName_child hdir hb), flCreat_ok,
      fun _ => hb1, .inr ⟨1, by decide, rfl, .inl ?_⟩⟩, hfr, hr⟩
    simp only [hcr, ↓reduceIte]
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsOsStep] at Hst
  obtain ⟨p', fl', hv, -, -, -, hres⟩ := Hst
  injection hv with hv1 hv2
  cases go.intoVal_inj hv1; cases go.intoVal_inj hv2
  simp only [hcr, htr, hacc, Bool.false_eq_true, ↓reduceIte] at hres
  imod gAuth_update _ _ _ _ _ false $$ HAz Hz with ⟨HAz, Hz⟩
  rw [busyMap_insert]
  rcases hres with ⟨st1, tgt, fd, heff, hfree, hst, rfl⟩ | ⟨e, he, rfl, hst⟩
  · unfold NsOpenEffect at heff
    rw [show st.nsFree.ns = st.ns from rfl, hfile] at heff
    obtain ⟨⟨f', -, hst1⟩, rfl⟩ := heff
    simp only [Bool.false_eq_true, ↓reduceIte] at hst1
    subst st1
    obtain ⟨hfd0, hfdn, hdfn⟩ := hfree
    have hfdn' : st.fds !! fd = none := hfdn
    have hdfn' : st.dfds !! fd = none := hdfn
    have hΓf : Γf !! fd = none := by rw [hcoh.fds]; exact hfdn'
    imod gAuth_insert _ _ _ fd (⟨k, true, true⟩ : OsFd) hΓf $$ HAf with ⟨HAf, Hfd⟩
    have hst' : st' = { st.nsFree with fds := <[fd := ⟨k, true, true⟩]> st.nsFree.fds } := by
      rw [hst]; simp [O_WRONLY, O_RDONLY]
    subst hst'
    have hwf0 := osWf_filesSame (filesSame_nsFree st) hwf
    have hcoh0 := osCoh_filesSame (filesSame_nsFree st) hcoh
    have hwf' := osWf_addFd hwf0 fd ⟨k, true, true⟩ ⟨f, hfk⟩
    have hcv : cellView { st.nsFree with fds := <[fd := ⟨k, true, true⟩]> st.nsFree.fds } =
        cellView st := cellView_congr rfl rfl rfl
    imod cells_same hwf hwf' Hr Hfr rfl hcv $$ [Hσ Hcells] with ⟨Hσ, Hcells⟩
    · iframe
    have hw' : NsWf { st.nsFree with fds := <[fd := ⟨k, true, true⟩]> st.nsFree.fds } := by
      refine ⟨hw.roots, hw.replay, hw.hist, hw.legacy, hw.dfds, fun fd' h' => ?_⟩
      show st.dfds !! fd' = none
      by_cases he : fd = fd'
      · subst he; exact hdfn'
      · apply hw.disj fd'
        have h'' : (<[fd := (⟨k, true, true⟩ : OsFd)]> st.fds) !! fd' ≠ none := h'
        rwa [GMap.lookup_insert_ne _ _ he] at h''
    have hcoh' : OsCoh { st.nsFree with fds := <[fd := ⟨k, true, true⟩]> st.nsFree.fds } Γb Γm
        (<[fd := ⟨k, true, true⟩]> Γf) Γt := by
      have : Γf = st.nsFree.fds := by rw [hcoh.fds]; rfl
      rw [this]; exact osCoh_fds hcoh0 _
    ihave Htok : tokRes (gooseOsGS (L := L))
        { st.nsFree with fds := <[fd := ⟨k, true, true⟩]> st.nsFree.fds } Γt $$ [Htok]
    · rw [show tokRes (gooseOsGS (L := L))
          { st.nsFree with fds := <[fd := ⟨k, true, true⟩]> st.nsFree.fds } Γt =
          tokRes (gooseOsGS (L := L)) st Γt from rfl]
      iexact Htok
    ihave Hwn := worlds_fold ⟨hwf', hcoh'⟩ ⟨hw', hc.congr rfl rfl rfl⟩ false rfl
      $$ HAb HAm HAf HAt Htok Hcells Hσ HAd HAdf HAz Hrd
    icases Hwn with ⟨Hw, Hn⟩
    imodintro
    iexists Γb, Γm, (<[fd := ⟨k, true, true⟩]> Γf), Γt, Γd, Γdf
    unfold osWorld nsWorld
    iframe Hw Hn
    iapply wp_value'
    iapply HΦ $$ %fd %0 %hmo %(.inl ⟨rfl, hfd0⟩) Hd Hm Hz
    rw [if_pos rfl]; unfold osFd; iexact Hfd
  · have hst' : st' = st.nsFree := by
      rcases hst with rfl | ⟨tgt, heff⟩
      · rfl
      · unfold NsOpenEffect at heff; rw [show st.nsFree.ns = st.ns from rfl, hfile] at heff
        obtain ⟨⟨f', -, h1⟩, -⟩ := heff
        simpa using h1
    subst hst'
    imod ns_step_close hwf hcoh (filesSame_nsFree st) Hr Hfr (nsWf_nsFree hw) (nsCoh_nsFree hc)
      false rfl $$ HAb HAm HAf HAt Htok Hcells Hσ HAd HAdf HAz Hrd with ⟨Hw, Hn⟩
    imodintro
    iexists Γb, Γm, Γf, Γt, Γd, Γdf
    unfold osWorld nsWorld
    iframe Hw Hn
    iapply wp_value'
    iapply HΦ $$ %(-1) %e %hmo %(.inr ⟨he, rfl⟩) Hd Hm Hz
    rw [if_neg he]; iempintro

end specs

end Perennial
