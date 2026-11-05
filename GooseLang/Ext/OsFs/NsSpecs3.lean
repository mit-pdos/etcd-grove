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
theorem nsCoh_addDirFd {st : OsState} {Γd Γdf} (hc : NsCoh st Γd Γdf) {fd : w64} {d : GoString} :
    NsCoh { st with dfds := <[fd := ⟨d, .idle⟩]> st.dfds } Γd (<[fd := (d, .idle)]> Γdf) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hc
  refine ⟨h1, h2, h3, h4, fun fd' => ?_, fun fd' x df hx hdf => ?_, fun fd' e rs g q hx => ?_⟩
  · show ((<[fd := (d, DirPh.idle)]> Γdf) !! fd').map (·.1) =
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
    · cases hx
    · exact h7 fd' e rs g q hx

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
theorem create_facts {st : OsState} {Γb Γm Γf Γt Γd Γdf} {d b k : GoString} {g : DirG}
    (hwf : OsWf st) (hcoh : OsCoh st Γb Γm Γf Γt) (hw : NsWf st) (hc : NsCoh st Γd Γdf)
    (hg : Γd !! d = some g) (hnr : ∀ fd rs g' q, Γdf !! fd ≠ some (d, .reading rs g' q))
    (hdir : st.ns !! d = some .dir) (hb : NameOk b) (hnone : st.ns !! child d b = none)
    (hk : IsInoKey k) (hkf : k ∉ st.files) :
    OsWf (createdSt st d b k) ∧ OsCoh (createdSt st d b k) Γb (<[k := some newMeta]> Γm) Γf Γt ∧
    cellView (createdSt st d b k) = cellView st ∧
    (∀ q, (createdSt st d b k).size q = st.size q) ∧
    NsWf (createdSt st d b k) ∧
    NsCoh (createdSt st d b k) (<[d := g.push (.put b (.file k))]> Γd) Γdf ∧
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
  have hop : FileOp st.ns (.create (child d b) k) :=
    ⟨hnone, ⟨d, parentOf_child' d b hb, hdir⟩, by rw [baseOf_child' d b hb]; exact hb⟩
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
  have hcB : NsCoh (createdSt st d b k) (<[d := g.push (.put b (.file k))]> Γd) Γdf :=
    nsCoh_fileOp hc hg hnr hop hin rfl rfl rfl rfl hw.replay
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
theorem worlds_fold {st' : OsState} {Γb Γm Γf Γt} {Γd : GMap GoString DirG}
    {Γdf : GMap w64 (GoString × DirPh)} {h' : GMap Loc (NonAtomic val)}
    (hwc : OsWf st' ∧ OsCoh st' Γb Γm Γf Γt) (hns : NsWf st' ∧ NsCoh st' Γd Γdf) (bz : Bool)
    (hbz : st'.nsBusy = bz) :
    ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb Γb -∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm Γm -∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γf Γf -∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γt Γt -∗
      tokRes (gooseOsGS (L := L)) st' Γt -∗ cellsRes (GF := GF) (cellView st') -∗ naHeapCtx tls h' -∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γd Γd -∗
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

/-- `open(2)` of a directory read-only: a new directory fd, not read, or an errno. -/
theorem wp_osNsOpenDir (d : GoString) (dq : DFrac) (g : DirG) (hE : ↑osN ⊆ E)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osDir (L := L) d dq g -∗
      (∀ fd : w64, ∀ e : w64, ⌜(e = 0 ∧ 0 ≤ fd.toInt) ∨ (e ≠ 0 ∧ fd = -1)⌝ -∗ osDir (L := L) d dq g -∗
        (if e = 0 then osDirFd (L := L) fd (DFrac.own 1) (d, .idle) else emp) -∗
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
  unfold osDir
  icases gAuth_lookup _ _ _ _ _ _ $$ HAd Hd with %Hdl
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hdir : st.ns !! d = some .dir := (hc.dirs d).1 (by rw [Hdl]; rfl)
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
    imod gAuth_insert _ _ _ fd (d, DirPh.idle) hΓ $$ HAdf with ⟨HAdf, Hfd⟩
    have hs : FilesSame st st' := by rw [hst]; exact ⟨rfl, rfl, rfl, rfl⟩
    have hw' : NsWf st' := by rw [hst]; exact nsWf_addDirFd hw hfdn hdir
    have hc' : NsCoh st' Γd (<[fd := (d, DirPh.idle)]> Γdf) := by
      rw [hst]; exact nsCoh_addDirFd hc
    ihave Hrd : rdRes (gooseOsGS (L := L)) (<[fd := (d, DirPh.idle)]> Γdf) $$ [Hrd]
    · unfold rdRes
      iapply (BigSepM.bigSepM_insert (M := GMap w64)
        (Φ := fun (_ : w64) (x : GoString × DirPh) => rdPart (gooseOsGS (L := L)) x) hΓ).2
      iframe; unfold rdPart; iempintro
    imod ns_step_close hwf hcoh hs Hr Hfr hw' hc' st.nsBusy (by rw [hst]) $$ HAb HAm HAf HAt Htok
      Hcells Hσ HAd HAdf HAz Hrd with ⟨Hw, Hn⟩
    imodintro
    iexists Γb, Γm, Γf, Γt, Γd, (<[fd := (d, DirPh.idle)]> Γdf)
    unfold osWorld nsWorld rdRes
    iframe Hw Hn
    iapply wp_value'
    iapply HΦ $$ %fd %0 %(.inl ⟨rfl, hfd0⟩) Hd
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
    iapply HΦ $$ %(-1) %e %(.inr ⟨he, rfl⟩) Hd
    rw [if_neg he]; iempintro

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
  unfold osDir osMeta
  icases gAuth_lookup _ _ _ _ _ _ $$ HAd Hd with %Hdl
  icases gAuth_lookup _ _ _ _ _ _ $$ HAm Hm with %Hml
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hdir : st.ns !! d = some .dir := (hc.dirs d).1 (by rw [Hdl]; rfl)
  have hfile : st.ns !! child d b = some (.file k) := by
    rw [← entsOf_child st.ns d b hb, hc.now d g Hdl]; exact hf
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
    · ipureintro; exact ⟨hw', hc.congr rfl rfl rfl rfl⟩
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
  unfold osDir osNsBusy
  icases gAuth_lookup _ _ _ _ _ _ $$ HAd Hd with %Hdl
  icases gAuth_lookup _ _ _ _ _ _ $$ HAz Hz with %Hzl
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hb1 : st.nsBusy = true := by
    simp only [busyMap, GMap.lookup_singleton_eq, Option.some.injEq] at Hzl; exact Hzl
  have hdir : st.ns !! d = some .dir := (hc.dirs d).1 (by rw [Hdl]; rfl)
  have hnone : st.ns !! child d b = none := by
    rw [← entsOf_child st.ns d b hb, hc.now d g Hdl]; exact hn
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
        gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γd Γd -∗
        gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γd d (DFrac.own 1) g ==∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm (<[k := some newMeta]> Γm) ∗
        gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γd (<[d := g.push (.put b (.file k))]> Γd) ∗
        osDir (L := L) d (DFrac.own 1) (g.push (.put b (.file k))) ∗
        osMeta (L := L) k (DFrac.own 1) (some newMeta) := by
    intro k hk hkf
    obtain ⟨-, -, -, -, -, -, hΓm, -, -⟩ :=
      create_facts hwf hcoh hw hc Hdl Hnr hdir hb hnone hk hkf
    iintro HAm HAd Hd
    imod gAuth_insert _ _ _ k (some newMeta) hΓm $$ HAm with ⟨HAm, Hm⟩
    imod gAuth_update _ _ _ _ _ (g.push (.put b (.file k))) $$ HAd Hd with ⟨HAd, Hd⟩
    imodintro
    unfold osDir osMeta
    iframe
  rcases hres with ⟨st1, tgt, fd, heff, hfree, hst, rfl⟩ | ⟨e, he, rfl, hst | ⟨tgt, heff⟩⟩
  · -- success
    obtain ⟨k, hk, hkf, rfl, rfl⟩ := heffect st1 tgt heff
    obtain ⟨hwfB, hcohB, hcvB, hszB, hwB, hcB, -, hfkB, hbB⟩ :=
      create_facts hwf hcoh hw hc Hdl Hnr hdir hb hnone hk hkf
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
    ihave Hwn := worlds_fold ⟨hwf', hcoh'⟩ ⟨hw', hcB.congr rfl rfl rfl rfl⟩ false hbB
      $$ HAb HAm HAf HAt Htok Hcells Hσ HAd HAdf HAz Hrd
    icases Hwn with ⟨Hw, Hn⟩
    imodintro
    iexists Γb, (<[k := some newMeta]> Γm), (<[fd := ⟨k, true, true⟩]> Γf), Γt,
      (<[d := g.push (.put b (.file k))]> Γd), Γdf
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
    unfold osDir osMeta osFd
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
      create_facts hwf hcoh hw hc Hdl Hnr hdir hb hnone hk hkf
    imod hghost k hk hkf $$ HAm HAd Hd with ⟨HAm, HAd, Hd, Hm⟩
    imod cells_same hwf hwfB Hr Hfr rfl hcvB $$ [Hσ Hcells] with ⟨Hσ, Hcells⟩
    · iframe
    ihave Htok : tokRes (gooseOsGS (L := L)) (createdSt st d b k) Γt $$ [Htok]
    · rw [create_tokRes _ Γt hszB]; iexact Htok
    ihave Hwn := worlds_fold ⟨hwfB, hcohB⟩ ⟨hwB, hcB⟩ false hbB
      $$ HAb HAm HAf HAt Htok Hcells Hσ HAd HAdf HAz Hrd
    icases Hwn with ⟨Hw, Hn⟩
    imodintro
    iexists Γb, (<[k := some newMeta]> Γm), Γf, Γt, (<[d := g.push (.put b (.file k))]> Γd), Γdf
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
    unfold osDir osMeta
    iframe

end specs

end Perennial
