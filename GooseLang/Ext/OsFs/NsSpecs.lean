/-
WP specs of the namespace's operations (`GooseLang/Ext/OsFs/Impl.lean`, `notes/walfs-ext-plan.md`).
Untrusted.

**Resources** (the generation's ghost state, `Ghost.lean`):
* `osDir d dq g`: the directory `d` exists, and `g` (`DirG`) is what the ghost state knows of
  its entries: durable ones and the changes since (its entries now are `g.now`, a crash leaves
  some prefix of the changes replayed). Fractional; a change of the directory needs it whole, a
  read of it a fraction for the read's length.
* `osDirFd fd dq x`: `fd` is an open directory fd, on the path `x.1`, its read at `x.2`.
* `osNsBusy b`: whether a call that changes the namespace is in flight (`NsBegin` sets it, the
  call's step clears it). Exclusive.
-/
module

public import GooseLang.Ext.OsFs.Specs
public import GooseLang.Ext.OsFs.NsLemmas

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode
open goose_heap

/-! ## The files' part of a namespace step -/

/-- `st'` has `st`'s files, fds, changes in flight and mappings. -/
def FilesSame (st st' : OsState) : Prop :=
  st'.files = st.files ∧ st'.fds = st.fds ∧ st'.inflight = st.inflight ∧ st'.maps = st.maps

theorem osWf_filesSame {st st' : OsState} (h : FilesSame st st') (hw : OsWf st) : OsWf st' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  cases st; cases st'; simp only at h1 h2 h3 h4; subst h1 h2 h3 h4
  exact ⟨hw.fds, hw.maps, hw.maps_disj, hw.infl, hw.infl_disj, hw.sizes, hw.coherent⟩

theorem metaOk_filesSame {st st' : OsState} {p : GoString} {m : OsMeta} {f : OsFile}
    (h : FilesSame st st') (hm : MetaOk st p m f) : MetaOk st' p m f := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  cases st; cases st'; simp only at h1 h2 h3 h4; subst h1 h2 h3 h4
  exact ⟨hm.size, hm.named, hm.lo, hm.hi, hm.ok, hm.maps, hm.targets, hm.dur, hm.durLen⟩

theorem osCoh_filesSame {st st' : OsState} {Γb Γm Γf Γt} (h : FilesSame st st')
    (hc : OsCoh st Γb Γm Γf Γt) : OsCoh st' Γb Γm Γf Γt := by
  have hm : ∀ p m, Γm !! p = some (some m) → ∃ f, st'.files !! p = some (some f) ∧
      MetaOk st' p m f := fun p m hp => by
    obtain ⟨f, hf1, hf2⟩ := hc.meta_some p m hp
    exact ⟨f, by rw [h.1]; exact hf1, metaOk_filesSame h hf2⟩
  obtain ⟨h1, h2, h3, h4⟩ := h
  cases st; cases st'; simp only at h1 h2 h3 h4; subst h1 h2 h3 h4
  exact ⟨hc.meta_dom, hc.meta_none, hm, hc.bytes, hc.bytes_full, hc.fds, hc.toks, hc.tok_q,
    hc.tok_alone, hc.tok_saved, hc.tok_clean⟩

theorem tokRes_filesSame {GF : BundledGFunctors} (hL : OsGS GF) {st st' : OsState} (Γt)
    (h : FilesSame st st') : tokRes hL st' Γt = tokRes hL st Γt := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  cases st; cases st'; simp only at h1 h2 h3 h4; subst h1 h2 h3 h4; rfl

theorem cellView_filesSame {st st' : OsState} (h : FilesSame st st') :
    cellView st' = cellView st :=
  cellView_congr h.2.2.2 h.1 h.2.2.1

section step
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- What a namespace operation's proof works with of the namespace: the state's facts, the
ghost maps of the directories and directory fds, the in-flight flag, and the fractions the reads
in progress hold. -/
def nsWorld (st : OsState) (Γd : GMap GoString DirG) (Γdf : GMap w64 (GoString × DirPh)) :
    IProp GF :=
  iprop(⌜NsWf st ∧ NsCoh st Γd Γdf⌝ ∗
    gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γd Γd ∗
    gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γdf Γdf ∗
    gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γz (busyMap st.nsBusy) ∗
    rdRes (gooseOsGS (L := L)) Γdf)

/-- The lifting of an operation of the namespace: as `wp_os_step`, with the namespace's world
too (`nsWorld`). -/
theorem wp_os_stepN (o : String) (v : val) (Φ : val → IProp GF) (hv : v.isPanic = false)
    (hE : ↑osN ⊆ E) :
    ⊢ osInv (L := L) -∗
      (∀ st Γb Γm Γf Γt Γd Γdf h, osWorld st Γb Γm Γf Γt h -∗ nsWorld st Γd Γdf ==∗
        ⌜∃ e' h' st', OsStep o v h st () e' h' st' ()⌝ ∗
        ▷ ∀ e' h' st', ⌜OsStep o v h st () e' h' st' ()⌝ ==∗
          ∃ Γb' Γm' Γf' Γt' Γd' Γdf', osWorld st' Γb' Γm' Γf' Γt' h' ∗
            nsWorld st' Γd' Γdf' ∗ WP e' @ s; E {{ Φ }}) -∗
      WP (ExternalOp osFsExt.name o (Val v)) @ s; E {{ Φ }} := by
  iintro #Hinv HF
  iapply wp_extStep o v Φ hv
  iintro %h %σ %g Hheap Hl -
  icases (os_local_ctx_eq σ).mp $$ Hl with Hl
  unfold osCtx osCtxF nsCtx
  icases Hl with ⟨⟨%Γb, %Γm, %Γf, %Γt, %Hwc, HAb, HAm, HAf, HAt, Htok, Hv⟩,
    ⟨%Γd, %Γdf, %Hns, HAd, HAdf, HAz, Hrd⟩⟩
  unfold osInv
  imod inv_acc hE $$ Hinv with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  icases Hi with ⟨%cv, %n, Hv', Hcells⟩
  icases gVar_agree _ _ _ _ _ $$ Hv Hv' with %Heq
  simp only [Prod.mk.injEq] at Heq
  obtain ⟨rfl, rfl⟩ := Heq
  imod HF $$ %σ %Γb %Γm %Γf %Γt %Γd %Γdf %h [HAb HAm HAf HAt Htok Hcells Hheap]
    [HAd HAdf HAz Hrd] with ⟨%Hex, Hcont⟩
  · unfold osWorld; iframe; ipureintro; exact Hwc
  · unfold nsWorld; iframe; ipureintro; exact Hns
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ E \ ↑osN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isplitr
  · ipureintro
    obtain ⟨e', h', st', Hst⟩ := Hex
    exact ⟨e', h', st', g, Hst⟩
  inext
  iintro %e' %h' %σ' %g' %Hst -
  imod Hclose2
  imod Hcont $$ %e' %h' %σ' %Hst with ⟨%Γb', %Γm', %Γf', %Γt', %Γd', %Γdf', Hw, Hn, Hwp⟩
  unfold osWorld
  icases Hw with ⟨%Hwc', HAb, HAm, HAf, HAt, Htok, Hcells, Hheap⟩
  imod gVar_update _ _ _ (cellView σ', GMap.size σ'.inflight) $$ Hv Hv' with ⟨Hv, Hv'⟩
  imod Hclose $$ [Hv' Hcells] with -
  · inext; iexists (cellView σ'), (GMap.size σ'.inflight); iframe
  imodintro
  iframe Hheap Hwp
  isplitl [HAb HAm HAf HAt Htok Hv Hn]
  · iapply (os_local_ctx_eq σ').mpr
    unfold osCtx osCtxF nsCtx
    isplitl [HAb HAm HAf HAt Htok Hv]
    · iexists Γb', Γm', Γf', Γt'
      iframe
      ipureintro; exact Hwc'
    · unfold nsWorld
      icases Hn with ⟨%Hns', HAd, HAdf, HAz, Hrd⟩
      iexists Γd', Γdf'
      iframe
      ipureintro; exact Hns'
  · have : (ExtInterp.globalCtx (E := osFsExt) (extGlobalGS osFsExt) g' : IProp GF) =
        iprop(True) := rfl
    rw [this]; itrivial

/-- The files' world after a step that leaves them alone. -/
theorem osWorld_filesSame {st st' : OsState} {Γb Γm Γf Γt} {h h' : GMap Loc (NonAtomic val)}
    (hs : FilesSame st st') (hr : HeapRendered st st' h h') (hfr : MapsFresh st st' h) :
    osWorld (L := L) st Γb Γm Γf Γt h ⊢ |==> osWorld (L := L) st' Γb Γm Γf Γt h' := by
  unfold osWorld
  iintro ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  have hwf' := osWf_filesSame hs hwf
  imod cells_same hwf hwf' hr hfr hs.2.2.2 (cellView_filesSame hs) $$ [Hσ Hcells]
    with ⟨Hσ, Hcells⟩
  · iframe
  rw [tokRes_filesSame _ Γt hs]
  imodintro
  iframe
  ipureintro; exact ⟨hwf', osCoh_filesSame hs hcoh⟩

end step

/-! ## Resources -/

section resources
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- The directory `d`, as `g` says. -/
def osDir (d : GoString) (dq : DFrac) (g : DirG) : IProp GF :=
  gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γd d dq g

/-- The directory fd `fd`, on `x.1`, its read at `x.2`. -/
def osDirFd (fd : w64) (dq : DFrac) (x : GoString × DirPh) : IProp GF :=
  gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γdf fd dq x

/-- Whether a call that changes the namespace is in flight. -/
def osNsBusy (b : Bool) : IProp GF :=
  gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γz () (DFrac.own 1) b

instance osDir_timeless (d : GoString) (dq : DFrac) (g : DirG) :
    Timeless (osDir (L := L) d dq g) := by unfold osDir; infer_instance
instance osDirFd_timeless (fd : w64) (dq : DFrac) (x : GoString × DirPh) :
    Timeless (osDirFd (L := L) fd dq x) := by unfold osDirFd; infer_instance
instance osNsBusy_timeless (b : Bool) : Timeless (osNsBusy (L := L) b) := by
  unfold osNsBusy; infer_instance

end resources

/-! ## Specs -/

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- A step that leaves the files alone exists from any heap the cells' view agrees with. -/
theorem step_filesSame {st st' : OsState} {h : GMap Loc (NonAtomic val)} (hwf : OsWf st)
    (hs : FilesSame st st')
    (Hag : ∀ l x, cellView st !! l = some x → ∃ m, h !! l = some (m, toCellVal x.1)) :
    MapsFresh st st' h ∧ HeapRendered st st' h h :=
  ⟨mapsFresh_same hs.2.2.2,
    heapRendered_same (osWf_filesSame hs hwf) hs.2.2.2 (cellView_filesSame hs) Hag⟩

theorem filesSame_refl (st : OsState) : FilesSame st st := ⟨rfl, rfl, rfl, rfl⟩

/-- `Regime(p)` of a directory of the namespace, or of a valid name in it: `1`. -/
theorem wp_osRegimeNs (p d : GoString) (dq : DFrac) (g : DirG)
    (hp : p = d ∨ ∃ b, NameOk b ∧ p = child d b) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osDir (L := L) d dq g -∗
      (osDir (L := L) d dq g -∗ Φ (#(1 : w64))) -∗
      WP (ExternalOp osFsExt.name "Regime" (Val (#p))) @ s; E {{ Φ }} := by
  iintro #Hinv Hd HΦ
  iapply wp_os_stepN "Regime" _ Φ (by simp [val.isPanic]) hE $$ Hinv
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
  have hpf : p ∉ st.files := by
    rcases hp with rfl | ⟨b, hb, rfl⟩
    · exact hw.dir_not_files hdir
    · exact hw.child_not_files hdir hb
  imodintro
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) hwf (filesSame_refl st) Hag
    exact ⟨_, h, st, ⟨p, rfl, rfl, rfl⟩, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsOsStep] at Hst
  obtain ⟨p', hv, hst, rfl⟩ := Hst
  subst st'
  cases go.intoVal_inj hv
  imod osWorld_filesSame (filesSame_refl st) Hr Hfr $$ [HAb HAm HAf HAt Htok Hcells Hσ] with Hw
  · unfold osWorld; iframe; ipureintro; exact ⟨hwf, hcoh⟩
  imodintro
  iexists Γb, Γm, Γf, Γt, Γd, Γdf
  unfold osWorld
  icases Hw with ⟨%Hwc', HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  iframe
  isplitr
  · ipureintro; exact Hwc'
  isplitr
  · ipureintro; exact ⟨hw, hc⟩
  iapply wp_value'
  rw [if_neg hpf]
  iapply HΦ $$ Hd

/-- `FdKind(fd)` of a directory fd: `1`. -/
theorem wp_osFdKindDir (fd : w64) (dq : DFrac) (x : GoString × DirPh) (hE : ↑osN ⊆ E)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osDirFd (L := L) fd dq x -∗
      (osDirFd (L := L) fd dq x -∗ Φ (#(1 : w64))) -∗
      WP (ExternalOp osFsExt.name "FdKind" (Val (#fd))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd HΦ
  iapply wp_os_stepN "FdKind" _ Φ (by simp [val.isPanic]) hE $$ Hinv
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
  have hnf : st.fds !! fd = none := by
    cases h0 : st.fds !! fd with
    | none => rfl
    | some d => have := hw.disj fd (by rw [h0]; simp); rw [hdf] at this; cases this
  imodintro
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) hwf (filesSame_refl st) Hag
    exact ⟨_, h, st, ⟨fd, rfl, rfl, .inr ⟨hnf, ⟨df, hdf⟩, rfl⟩⟩, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsOsStep] at Hst
  obtain ⟨fd', hv, hst, hres⟩ := Hst
  subst st'
  cases go.intoVal_inj hv
  rcases hres with ⟨⟨d, hd⟩, -⟩ | ⟨-, -, rfl⟩
  · rw [hnf] at hd; cases hd
  imod osWorld_filesSame (filesSame_refl st) Hr Hfr $$ [HAb HAm HAf HAt Htok Hcells Hσ] with Hw
  · unfold osWorld; iframe; ipureintro; exact ⟨hwf, hcoh⟩
  imodintro
  iexists Γb, Γm, Γf, Γt, Γd, Γdf
  unfold osWorld
  icases Hw with ⟨%Hwc', HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  iframe
  isplitr
  · ipureintro; exact Hwc'
  isplitr
  · ipureintro; exact ⟨hw, hc⟩
  iapply wp_value'
  iapply HΦ $$ Hfd

/-- `NsBegin()`, with the in-flight flag unset: it is set. -/
theorem wp_osNsBegin (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osNsBusy (L := L) false -∗
      (osNsBusy (L := L) true -∗ Φ (#())) -∗
      WP (ExternalOp osFsExt.name "NsBegin" (Val (#()))) @ s; E {{ Φ }} := by
  iintro #Hinv Hz HΦ
  iapply wp_os_stepN "NsBegin" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %Γd %Γdf %h Hw Hn
  unfold osWorld nsWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases Hn with ⟨%Hns, HAd, HAdf, HAz, Hrd⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  obtain ⟨hw, hc⟩ := Hns
  unfold osNsBusy
  icases gAuth_lookup _ _ _ _ _ _ $$ HAz Hz with %Hzl
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hb : st.nsBusy = false := by
    simp only [busyMap, GMap.lookup_singleton_eq, Option.some.injEq] at Hzl; exact Hzl
  obtain ⟨st1, hst1⟩ : ∃ st1 : OsState, st1 = { st with nsBusy := true } := ⟨_, rfl⟩
  have hs : FilesSame st st1 := by subst hst1; exact ⟨rfl, rfl, rfl, rfl⟩
  imodintro
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) hwf hs Hag
    exact ⟨_, h, st1, ⟨rfl, hb, hst1, rfl⟩, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsOsStep] at Hst
  obtain ⟨-, -, hst', rfl⟩ := Hst
  have : st' = st1 := hst'.trans hst1.symm
  subst this
  imod osWorld_filesSame hs Hr Hfr $$ [HAb HAm HAf HAt Htok Hcells Hσ] with Hw
  · unfold osWorld; iframe; ipureintro; exact ⟨hwf, hcoh⟩
  imod gAuth_update _ _ _ _ _ true $$ HAz Hz with ⟨HAz, Hz⟩
  imodintro
  iexists Γb, Γm, Γf, Γt, Γd, Γdf
  unfold osWorld
  icases Hw with ⟨%Hwc', HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  have : (<[() := true]> (busyMap st.nsBusy)) = busyMap st'.nsBusy := by
    subst hst'; apply GMap.ext; intro u; cases u; simp [busyMap]
  rw [this] at *
  iframe
  isplitr
  · ipureintro; exact Hwc'
  isplitr
  · ipureintro
    subst hst'
    refine ⟨?_, hc.congr rfl rfl rfl rfl⟩
    exact ⟨hw.roots, hw.replay, hw.hist, hw.legacy, hw.dfds, hw.disj⟩
  iapply wp_value'
  iapply HΦ $$ Hz

end specs

end Perennial
