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

end Perennial
