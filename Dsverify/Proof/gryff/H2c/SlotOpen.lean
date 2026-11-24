/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H2c/SlotOpen.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit H2c: one instance slot open, with `crtInstance` and `epaxosRest` out

`epaxosOwn_slot_open`: `epaxosOwn_inst_open'` (H2's) with, in addition, the `crtInstance` slice,
its lower bounds' authorities and `epaxosRest` (`maxSeq`) out; the closings take them back at a
new `crtInstance` (`withCrt s l`). Used by the handlers that load an instance's pointer before
updating `maxSeq` / `crtInstance` (`handleCommit`, `handleAccept`).
-/
module

public import Dsverify.Proof.gryff.H2.InstOpen

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (RState Copy LB Proposal Msg Ev Out Cmd Deps)
open Perennial.gryff.replica (XS rowOwn nSlots)

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- `s` with `crtInstance := l`. -/
def withCrt (s : RState) (l : List w32) : RState := { s with crtInstance := l }

@[simp] theorem withCrt_crtInstance (s : RState) (l : List w32) :
    (withCrt s l).crtInstance = l := rfl
@[simp] theorem withCrt_inst (s : RState) (l : List w32) : (withCrt s l).inst = s.inst := rfl
@[simp] theorem withCrt_confAt (s : RState) (l : List w32) :
    (withCrt s l).confAt = s.confAt := rfl
@[simp] theorem withCrt_maxSeqK0 (s : RState) (l : List w32) :
    (withCrt s l).maxSeqK0 = s.maxSeqK0 := rfl
@[simp] theorem withCrt_self (s : RState) : withCrt s s.crtInstance = s := rfl
theorem setCrt_eq_withCrt (s : RState) (q x : w32) :
    s.setCrt q x = withCrt s (s.crtInstance.set q.toNat x) := rfl

theorem committedOrExecuted_withCrt (s : RState) (l : List w32) :
    committedOrExecuted (withCrt s l) = committedOrExecuted s := rfl

/-- `setInst` at a slot that already holds the copy. -/
theorem setInst_self (s : RState) (q i : w32) (c : Copy) (h : s.inst q i = some c) :
    s.setInst q i c = s := by
  cases s
  simp only [model.RState.setInst, model.RState.mk.injEq, true_and, and_true]
  funext q' i'
  split
  · rename_i e; obtain ⟨rfl, rfl⟩ := e; exact h.symm
  · rfl

variable [GooseExts] [GoGlobalContext] in
theorem epFacts_withCrt (xs : XS) (s : RState) (isp : List GoSlice) (cfs : List Loc)
    (M : GMap replica.Node Loc) (cu : GoArray w32 5) (pm : GMap w64 src.gryffproto.ValTag)
    (l : List w32) (hl : l.length = 3) (Hf : epFacts xs s isp cfs M cu pm) :
    epFacts xs (withCrt s l) isp cfs M cu pm := by
  obtain ⟨h1, h2, _, h4, h5, h6, h7, h8, h9, h10, h11⟩ := Hf
  exact ⟨h1, h2, hl, h4, h5, h6, h7, h8, h9, h10, h11⟩

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]


/-- `crtInstance`'s lower bounds' authorities at `s`. -/
abbrev crtMonos (ρ : Repl2Names) (s : RState) : IProp GF :=
  iprop([∗list] q ∈ List.finRange 3, monoNatAuthOwn (ρ.crt q) 1 (sint.Z (s.crt (rid32 q))).toNat)

/-- A committed (or executed) slot's pointer is fixed for good: its `ρ.ptrs` element, persistent. -/
def elemIf (ρ : Repl2Names) (s : RState) (n : replica.Node) (p : Loc) : IProp GF :=
  if committedOrExecuted s n then ghostMapElem ρ.ptrs n DFrac.discard p else iprop(True)

instance elemIf_persistent (ρ : Repl2Names) (s : RState) (n : replica.Node) (p : Loc) :
    Persistent (elemIf (GF := GF) ρ s n p) := by
  unfold elemIf; split <;> infer_instance

theorem elem_dup (ρ : Repl2Names) (s : RState) (n : replica.Node) (p : Loc) :
    (ghostMapElem ρ.ptrs n (if committedOrExecuted s n then DFrac.discard else DFrac.own 1) p :
      IProp GF) ⊢ elemIf ρ s n p ∗
      ghostMapElem ρ.ptrs n (if committedOrExecuted s n then DFrac.discard else DFrac.own 1) p := by
  unfold elemIf
  cases committedOrExecuted s n
  · simp only [Bool.false_eq_true, ↓reduceIte]; iintro H; iframe H
  · simp only [↓reduceIte]; iintro #H; iframe H

/-- Two elements of one node agree. -/
theorem elemIf_agree (ρ : Repl2Names) (s s' : RState) (n : replica.Node) (p p' : Loc)
    (h : committedOrExecuted s n = true) (h' : committedOrExecuted s' n = true) :
    elemIf ρ s n p ∗ elemIf ρ s' n p' ⊢ (⌜p = p'⌝ : IProp GF) := by
  unfold elemIf
  rw [h, h']
  simp only [↓reduceIte]
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %He
  ipureintro; exact He.2

set_option maxHeartbeats 1000000 in
/-- **One slot open, `crtInstance` and `epaxosRest` out.** -/
theorem epaxosOwn_slot_open (ρ : Repl2Names) (h r : Loc) (xs : XS) (s : RState) (q i : w32)
    (hb : model.inBox q i = true) :
    epaxosOwn (GF := GF) ρ h r xs s ⊢ ∃ (ispS sq crtS : GoSlice) (isp : List GoSlice) (ptrs : List Loc) (p : Loc),
      h.[src.gryff.EPaxosRMWHandler, go!"R"] ↦□ r ∗
      h.[src.gryff.EPaxosRMWHandler, go!"InstanceSpace"] ↦□ ispS ∗ ispS ↦*□ isp ∗
      ⌜isp[(sint.Z q).toNat]? = some sq ∧ ptrs[(sint.Z i).toNat]? = some p ∧
        s.crtInstance.length = 3⌝ ∗ sq ↦* ptrs ∗
      (match s.inst q i with
       | none => iprop(⌜p = Loc.null⌝)
       | some c => iprop(⌜p ≠ Loc.null⌝ ∗ copyRep ρ xs (sint.Z q, sint.Z i) p c)) ∗
      ⌜committedOrExecuted s (sint.Z q, sint.Z i) = false →
        xs.numF (sint.Z q, sint.Z i) = 0 ∧ xs.lowF (sint.Z q, sint.Z i) = 0 ∧
        (sint.Z q, sint.Z i) ∉ xs.1⌝ ∗ elemIf ρ s (sint.Z q, sint.Z i) p ∗
      h.[src.gryff.EPaxosRMWHandler, go!"crtInstance"] ↦□ crtS ∗ crtS ↦* s.crtInstance ∗
      crtMonos ρ s ∗ epaxosRest h ∗
      (∀ l : List w32, ⌜l.length = 3⌝ -∗ crtS ↦* l -∗ crtMonos ρ (withCrt s l) -∗ epaxosRest h -∗
       -- (a) the same pointer, a new copy
       ((∀ c' : Copy, ⌜(s.inst q i).isSome ∧ (committedOrExecuted s (sint.Z q, sint.Z i) = true →
            committedOrExecuted (s.setInst q i c') (sint.Z q, sint.Z i) = true)⌝ -∗
          sq ↦* ptrs -∗ copyRep ρ xs (sint.Z q, sint.Z i) p c' -∗
          |==> (epaxosOwn ρ h r xs ((withCrt s l).setInst q i c') ∗
            elemIf ρ ((withCrt s l).setInst q i c') (sint.Z q, sint.Z i) p)) ∧
       -- (b) a fresh pointer in a nil slot
       (∀ (p' : Loc) (c' : Copy), ⌜s.inst q i = none ∧ p' ≠ Loc.null⌝ -∗
          sq ↦* ptrs.set (sint.Z i).toNat p' -∗ copyRep ρ xs (sint.Z q, sint.Z i) p' c' -∗
          |==> epaxosOwn ρ h r xs ((withCrt s l).setInst q i c')) ∧
       -- (c) a fresh pointer replacing an uncommitted copy's
       (∀ (p' : Loc) (c' : Copy), ⌜(s.inst q i).isSome ∧
            committedOrExecuted s (sint.Z q, sint.Z i) = false ∧ p' ≠ Loc.null⌝ -∗
          sq ↦* ptrs.set (sint.Z i).toNat p' -∗ copyRep ρ xs (sint.Z q, sint.Z i) p' c' -∗
          |==> epaxosOwn ρ h r xs ((withCrt s l).setInst q i c')) ∧
       -- (a0) the same pointer, a new copy of the same committedness (no update)
       (∀ c' : Copy, ⌜(s.inst q i).isSome ∧ committedOrExecuted (s.setInst q i c') (sint.Z q, sint.Z i) =
            committedOrExecuted s (sint.Z q, sint.Z i)⌝ -∗
          sq ↦* ptrs -∗ copyRep ρ xs (sint.Z q, sint.Z i) p c' -∗
          epaxosOwn ρ h r xs ((withCrt s l).setInst q i c')))) := by
  have hb' := of_decide_eq_true hb
  obtain ⟨hq0, hq3, hi0, hiS⟩ := hb'
  unfold model.SLOTS at hiS
  have hqN : ((sint.Z q).toNat : Int) = sint.Z q := by omega
  have hiN : ((sint.Z i).toNat : Int) = sint.Z i := by omega
  iintro H
  icases (epaxosOwn_open ..).1 $$ H with ⟨%ispS, %crtS, %c1S, %isp, %msR, %pvtR, %cfs, %M, %cu,
    %pm, #HR, #HnoC, #HispS, #Hisp, #HcrtS, #Hc1S, #Hcfs, #HmsR, #HpvtR, Hcu, Hcrt, HM, HMe,
    Hrows, Hinsts, Hmono, Hconfs, Hms, Hpm, Hrest, %Hf⟩
  obtain ⟨sq, hsq⟩ : ∃ sq, isp[(sint.Z q).toNat]? = some sq :=
    ⟨_, List.getElem?_eq_getElem (by rw [Hf.1]; omega)⟩
  icases rows_acc' M isp _ sq hsq $$ Hrows with ⟨Hrow, Hrows⟩
  icases (replica.rowOwn_open ..).1 $$ Hrow with ⟨%ptrs, Hrow, %Hrowf⟩
  obtain ⟨p, hp⟩ : ∃ p, ptrs[(sint.Z i).toNat]? = some p :=
    ⟨_, List.getElem?_eq_getElem (by rw [Hrowf.1]; unfold nSlots; omega)⟩
  have hMp := Hrowf.2 _ p hp
  rw [hqN, hiN] at hMp
  have hinst := Hf.2.2.2.2.2.2.1 q i hb
  have hxs : committedOrExecuted s (sint.Z q, sint.Z i) = false →
      xs.numF (sint.Z q, sint.Z i) = 0 ∧ xs.lowF (sint.Z q, sint.Z i) = 0 ∧
      (sint.Z q, sint.Z i) ∉ xs.1 := by
    intro hc
    have h10 := Hf.2.2.2.2.2.2.2.2.2.1 (sint.Z q, sint.Z i)
    rw [hc] at h10
    refine ⟨?_, ?_, ?_⟩
    · exact Decidable.byContradiction fun hh => absurd (h10 (.inr (.inl hh))) (by simp)
    · exact Decidable.byContradiction fun hh => absurd (h10 (.inr (.inr hh))) (by simp)
    · exact fun hh => absurd (h10 (.inl hh)) (by simp)
  iexists ispS, sq, crtS, isp, ptrs, p
  isplitr; · iexact HR
  isplitr; · iexact HispS
  isplitr; · iexact Hisp
  isplitr; · ipureintro; exact ⟨hsq, hp, Hf.2.2.1⟩
  iframe Hrow
  rcases hsi : s.inst q i with _ | c
  · -- an empty slot
    have hMn : M.lookup (sint.Z q, sint.Z i) = none := by
      rw [hsi] at hinst; simpa using hinst.symm
    have hpn : p = Loc.null := by
      rw [hMn] at hMp; split at hMp
      · assumption
      · cases hMp
    isplitr; · ipureintro; exact hpn
    isplitr; · ipureintro; exact hxs
    have hco0 : committedOrExecuted s (sint.Z q, sint.Z i) = false := by
      simp only [committedOrExecuted, model.committedCopy, BitVec.ofInt_toInt, hsi]
      split <;> rfl
    isplitr; · unfold elemIf; rw [hco0]; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
    iframe HcrtS Hcrt Hmono Hrest
    iintro %l %hl Hcrt Hmono Hrest
    isplit
    · iintro %c' %hc'; simp at hc'
    isplit
    · iintro %p' %c' %hc' Hrow Hc'
      imod ghost_map_insert (γ := ρ.ptrs) (sint.Z q, sint.Z i) p' hMn $$ HM with ⟨HM, Hel⟩
      ihave >Hel := elem_upd ρ (sint.Z q, sint.Z i) p' false
        (committedOrExecuted ((withCrt s l).setInst q i c') (sint.Z q, sint.Z i)) (by simp) $$ [Hel]
      · simp only [Bool.false_eq_true, ↓reduceIte]; iexact Hel
      ihave Hrow := rowOwn_insert M _ _ sq ptrs p' hc'.2 Hrowf.1 Hrowf.2 $$ Hrow
      simp only [hqN, hiN]
      ihave Hrows := Hrows $$ %(GMap.insert (sint.Z q, sint.Z i) p' M) %?_ Hrow
      · intro k j hk
        rw [GMap.lookup_insert_ne _ _ (by intro e; simp only [Prod.mk.injEq] at e; omega)]
      ihave Hinsts := insts_insert ρ xs s ((withCrt s l).setInst q i c') M q i p' c' hMn
        (by simp [model.RState.setInst, withCrt])
        (fun q' i' hne => by simp only [model.RState.setInst, hne, ↓reduceIte, withCrt])
        $$ [$Hinsts $Hc']
      imodintro
      iapply (epaxosOwn_open ..).2
      iexists ispS, crtS, c1S, isp, msR, pvtR, cfs, (GMap.insert (sint.Z q, sint.Z i) p' M), cu, pm
      simp only [setInst_crtInstance, setInst_crt, setInst_confAt, setInst_maxSeqK0,
        withCrt_crtInstance, withCrt_confAt, withCrt_maxSeqK0]
      iframe # ∗
      isplitl [HMe Hel]
      · iapply (BigSepM.bigSepM_insert (show get? M (sint.Z q, sint.Z i) = none from hMn)).2
        iframe Hel
        iapply BigSepM.bigSepM_mono (fun {n p0} hnp => ?_) $$ HMe
        have hne : n ≠ (sint.Z q, sint.Z i) := by
          intro e; subst e; rw [show get? M (sint.Z q, sint.Z i) = none from hMn] at hnp; cases hnp
        rw [committedOrExecuted_setInst (withCrt s l) q i c' n hne, committedOrExecuted_withCrt]
      · ipureintro
        exact epFacts_setInst xs (withCrt s l) isp cfs M _ cu pm q i c' p' hb
          (epFacts_withCrt xs s isp cfs M cu pm l hl Hf) (GMap.lookup_insert ..)
          (fun n hn => GMap.lookup_insert_ne _ _ (Ne.symm hn))
          (fun hx => by have := Hf.2.2.2.2.2.2.2.2.1 _ hx; rw [hMn] at this; cases this)
    isplit
    · iintro %p' %c' %hc'; simp at hc'
    · iintro %c' %hc'; simp at hc'
  · -- a copy
    have hpn : p ≠ Loc.null := by
      intro e; rw [e] at hMp; simp only [↓reduceIte] at hMp; rw [hsi, hMp] at hinst
      simp at hinst
    have hMs : M.lookup (sint.Z q, sint.Z i) = some p := by
      rw [hMp]; simp [hpn]
    icases insts_replace ρ xs s M q i p c hMs hsi $$ Hinsts with ⟨Hc, Hclose⟩
    icases (BigSepM.bigSepM_delete (show get? M (sint.Z q, sint.Z i) = some p from hMs)).1 $$ HMe
      with ⟨Hel, HMe⟩
    icases elem_dup ρ s (sint.Z q, sint.Z i) p $$ Hel with ⟨#HelP, Hel⟩
    dsimp only
    isplitl [Hc]
    · iframe Hc; ipureintro; exact hpn
    isplitr; · ipureintro; exact hxs
    iframe HelP HcrtS Hcrt Hmono Hrest
    iintro %l %hl Hcrt Hmono Hrest
    have hsc : ((withCrt s l).setInst q i c).inst q i = some c := by
      simp [model.RState.setInst]
    isplit
    · -- (a) the same pointer
      iintro %c' %hc' Hrow Hc'
      ihave >Hel := elem_upd ρ (sint.Z q, sint.Z i) p _
        (committedOrExecuted ((withCrt s l).setInst q i c') (sint.Z q, sint.Z i)) hc'.2 $$ Hel
      icases elem_dup ρ ((withCrt s l).setInst q i c') (sint.Z q, sint.Z i) p $$ Hel with ⟨#HelP', Hel⟩
      ihave Hrow := (replica.rowOwn_open M _ sq).2 $$ [Hrow]
      · iexists ptrs; iframe; ipureintro; exact Hrowf
      ihave Hrows := Hrows $$ %M %(fun _ _ _ => rfl) Hrow
      have hsc : ((withCrt s l).setInst q i c').inst q i = some c' ∧ ∀ q' i', ¬(q' = q ∧ i' = i) →
          ((withCrt s l).setInst q i c').inst q' i' = s.inst q' i' :=
        ⟨by simp [model.RState.setInst],
          fun q' i' hne => by simp only [model.RState.setInst, hne, ↓reduceIte, withCrt]⟩
      ihave Hinsts := Hclose $$ %((withCrt s l).setInst q i c') %p %c' %hsc Hc'
      rw [GMap.insert_id M _ p hMs]
      imodintro
      iframe HelP'
      iapply (epaxosOwn_open ..).2
      iexists ispS, crtS, c1S, isp, msR, pvtR, cfs, M, cu, pm
      simp only [setInst_crtInstance, setInst_crt, setInst_confAt, setInst_maxSeqK0,
        withCrt_crtInstance, withCrt_confAt, withCrt_maxSeqK0]
      iframe # ∗
      isplitl [HMe Hel]
      · iapply (BigSepM.bigSepM_delete (show get? M (sint.Z q, sint.Z i) = some p from hMs)).2
        iframe Hel
        iapply elems_congr ρ s ((withCrt s l).setInst q i c') M _
          (fun n hn => committedOrExecuted_setInst (withCrt s l) q i c' n hn) $$ HMe
      · ipureintro
        exact epFacts_setInst xs (withCrt s l) isp cfs M M cu pm q i c' p hb
          (epFacts_withCrt xs s isp cfs M cu pm l hl Hf) hMs (fun _ _ => rfl)
          (fun hx => hc'.2 (Hf.2.2.2.2.2.2.2.2.2.1 _ hx))
    isplit
    · iintro %p' %c' %hc'; simp at hc'
    isplit
    · -- (c) a fresh pointer replacing an uncommitted copy's
      iintro %p' %c' %hc' Hrow Hc'
      simp only [hc'.2.1, Bool.false_eq_true, ↓reduceIte]
      imod ghost_map_update (γ := ρ.ptrs) p' $$ HM Hel with ⟨HM, Hel⟩
      ihave >Hel := elem_upd ρ (sint.Z q, sint.Z i) p' false
        (committedOrExecuted ((withCrt s l).setInst q i c') (sint.Z q, sint.Z i)) (by simp) $$ [Hel]
      · simp only [Bool.false_eq_true, ↓reduceIte]; iexact Hel
      ihave Hrow := rowOwn_insert M _ _ sq ptrs p' hc'.2.2 Hrowf.1 Hrowf.2 $$ Hrow
      simp only [hqN, hiN]
      ihave Hrows := Hrows $$ %(GMap.insert (sint.Z q, sint.Z i) p' M) %?_ Hrow
      · intro k j hk
        rw [GMap.lookup_insert_ne _ _ (by intro e; simp only [Prod.mk.injEq] at e; omega)]
      have hsc : ((withCrt s l).setInst q i c').inst q i = some c' ∧ ∀ q' i', ¬(q' = q ∧ i' = i) →
          ((withCrt s l).setInst q i c').inst q' i' = s.inst q' i' :=
        ⟨by simp [model.RState.setInst],
          fun q' i' hne => by simp only [model.RState.setInst, hne, ↓reduceIte, withCrt]⟩
      ihave Hinsts := Hclose $$ %((withCrt s l).setInst q i c') %p' %c' %hsc Hc'
      imodintro
      iapply (epaxosOwn_open ..).2
      iexists ispS, crtS, c1S, isp, msR, pvtR, cfs, (GMap.insert (sint.Z q, sint.Z i) p' M), cu, pm
      simp only [setInst_crtInstance, setInst_crt, setInst_confAt, setInst_maxSeqK0,
        withCrt_crtInstance, withCrt_confAt, withCrt_maxSeqK0]
      iframe # ∗
      isplitl [HMe Hel]
      · rw [← GMap.insert_delete]
        iapply (BigSepM.bigSepM_insert (show get? (delete M (sint.Z q, sint.Z i))
          (sint.Z q, sint.Z i) = none from LawfulPartialMap.get?_delete_eq rfl)).2
        iframe Hel
        iapply elems_congr ρ s ((withCrt s l).setInst q i c') M _
          (fun n hn => committedOrExecuted_setInst (withCrt s l) q i c' n hn) $$ HMe
      · ipureintro
        exact epFacts_setInst xs (withCrt s l) isp cfs M _ cu pm q i c' p' hb
          (epFacts_withCrt xs s isp cfs M cu pm l hl Hf) (GMap.lookup_insert ..)
          (fun n hn => GMap.lookup_insert_ne _ _ (Ne.symm hn))
          (fun hx => absurd (Hf.2.2.2.2.2.2.2.2.2.1 _ hx) (by rw [hc'.2.1]; simp))
    · -- (a0) the same pointer, the same committedness
      iintro %c' %hc' Hrow Hc'
      have heq : committedOrExecuted ((withCrt s l).setInst q i c') (sint.Z q, sint.Z i) =
          committedOrExecuted s (sint.Z q, sint.Z i) := hc'.2
      ihave Hrow := (replica.rowOwn_open M _ sq).2 $$ [Hrow]
      · iexists ptrs; iframe; ipureintro; exact Hrowf
      ihave Hrows := Hrows $$ %M %(fun _ _ _ => rfl) Hrow
      have hsc : ((withCrt s l).setInst q i c').inst q i = some c' ∧ ∀ q' i', ¬(q' = q ∧ i' = i) →
          ((withCrt s l).setInst q i c').inst q' i' = s.inst q' i' :=
        ⟨by simp [model.RState.setInst],
          fun q' i' hne => by simp only [model.RState.setInst, hne, ↓reduceIte, withCrt]⟩
      ihave Hinsts := Hclose $$ %((withCrt s l).setInst q i c') %p %c' %hsc Hc'
      rw [GMap.insert_id M _ p hMs]
      iapply (epaxosOwn_open ..).2
      iexists ispS, crtS, c1S, isp, msR, pvtR, cfs, M, cu, pm
      simp only [setInst_crtInstance, setInst_crt, setInst_confAt, setInst_maxSeqK0,
        withCrt_crtInstance, withCrt_confAt, withCrt_maxSeqK0]
      iframe # ∗
      isplitl [HMe Hel]
      · iapply (BigSepM.bigSepM_delete (show get? M (sint.Z q, sint.Z i) = some p from hMs)).2
        rw [heq]
        iframe Hel
        iapply elems_congr ρ s ((withCrt s l).setInst q i c') M _
          (fun n hn => committedOrExecuted_setInst (withCrt s l) q i c' n hn) $$ HMe
      · ipureintro
        exact epFacts_setInst xs (withCrt s l) isp cfs M M cu pm q i c' p hb
          (epFacts_withCrt xs s isp cfs M cu pm l hl Hf) hMs (fun _ _ => rfl)
          (fun hx => by rw [heq]; exact Hf.2.2.2.2.2.2.2.2.2.1 _ hx)

end

end Perennial.gryff.replica2

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (RState Copy LB Proposal Msg Ev Out Cmd Deps)
open Perennial.gryff.replica (XS rowOwn nSlots)

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]


theorem cmdsRep_open (sl : GoSlice) (cs : List Cmd) :
    cmdsRep (GF := GF) sl cs ⊣⊢ ∃ gs : List src.state.Command, sl ↦*□ gs ∗
      ⌜gs.map cmdOf = cs ∧ model.cmdsOk cs⌝ := by
  unfold cmdsRep; exact .rfl

instance cmdsRep_persistent (sl : GoSlice) (cs : List Cmd) : Persistent (cmdsRep sl cs : IProp GF) := by
  unfold cmdsRep; infer_instance

theorem lbRep_none (ρ : Repl2Names) (l : Loc) : lbRep ρ l none ⊣⊢ (⌜l = Loc.null⌝ : IProp GF) := by
  unfold lbRep; exact .rfl

theorem lbRep_some (ρ : Repl2Names) (l : Loc) (b : LB) : lbRep (GF := GF) ρ l (some b) ⊣⊢
    ∃ g : src.gryff.LeaderBookkeeping, l ↦ g ∗
      proposalsRep ρ g.clientProposals' b.clientProposals ∗
      g.committedDeps' ↦* b.committedDeps ∗ riRep g.recoveryInst' b.recoveryInst ∗
      ⌜g.maxRecvBallot' = b.maxRecvBallot ∧ g.prepareOKs' = b.prepareOKs ∧
        g.allEqual' = b.allEqual ∧ g.preAcceptOKs' = b.preAcceptOKs ∧
        g.acceptOKs' = b.acceptOKs ∧ g.nacks' = b.nacks ∧ depsOf g.originalDeps' = b.originalDeps ∧
        g.preparing' = b.preparing ∧ g.numReplicasExecuted' = b.numReplicasExecuted ∧
        g.repliedClient' = b.repliedClient⌝ := by
  unfold lbRep; exact .rfl

/-- `epaxosOwn` does not depend on `ProposeChan`'s contents. -/
theorem epaxosOwn_proposeQ (ρ : Repl2Names) (h r : Loc) (xs : XS) (s : RState)
    (pq : List Proposal) :
    epaxosOwn (GF := GF) ρ h r xs s ⊢ epaxosOwn ρ h r xs { s with proposeQ := pq } := by
  unfold epaxosOwn; exact .rfl

/-- **A slot's pointer, read access** (the instance-space row out and back unchanged). -/
theorem epaxosOwn_peek (ρ : Repl2Names) (h r : Loc) (xs : XS) (s : RState) (q i : w32)
    (hb : model.inBox q i = true) :
    epaxosOwn (GF := GF) ρ h r xs s ⊢ ∃ (ispS sq : GoSlice) (isp : List GoSlice) (ptrs : List Loc) (p : Loc),
      h.[src.gryff.EPaxosRMWHandler, go!"InstanceSpace"] ↦□ ispS ∗ ispS ↦*□ isp ∗
      ⌜isp[(sint.Z q).toNat]? = some sq ∧ ptrs[(sint.Z i).toNat]? = some p⌝ ∗ sq ↦* ptrs ∗
      (sq ↦* ptrs -∗ epaxosOwn ρ h r xs s) := by
  have hb' := of_decide_eq_true hb
  obtain ⟨hq0, hq3, hi0, hiS⟩ := hb'
  unfold model.SLOTS at hiS
  iintro H
  icases (epaxosOwn_open ..).1 $$ H with ⟨%ispS, %crtS, %c1S, %isp, %msR, %pvtR, %cfs, %M, %cu,
    %pm, #HR, #HnoC, #HispS, #Hisp, #HcrtS, #Hc1S, #Hcfs, #HmsR, #HpvtR, Hcu, Hcrt, HM, HMe,
    Hrows, Hinsts, Hmono, Hconfs, Hms, Hpm, Hrest, %Hf⟩
  obtain ⟨sq, hsq⟩ : ∃ sq, isp[(sint.Z q).toNat]? = some sq :=
    ⟨_, List.getElem?_eq_getElem (by rw [Hf.1]; omega)⟩
  icases rows_acc' M isp _ sq hsq $$ Hrows with ⟨Hrow, Hrows⟩
  icases (replica.rowOwn_open ..).1 $$ Hrow with ⟨%ptrs, Hrow, %Hrowf⟩
  obtain ⟨p, hp⟩ : ∃ p, ptrs[(sint.Z i).toNat]? = some p :=
    ⟨_, List.getElem?_eq_getElem (by rw [Hrowf.1]; unfold nSlots; omega)⟩
  iexists ispS, sq, isp, ptrs, p
  iframe HispS Hisp Hrow
  isplitr; · ipureintro; exact ⟨hsq, hp⟩
  iintro Hrow
  ihave Hrow := (replica.rowOwn_open M _ sq).2 $$ [Hrow]
  · iexists ptrs; iframe; ipureintro; exact Hrowf
  ihave Hrows := Hrows $$ %M %(fun _ _ _ => rfl) Hrow
  iapply (epaxosOwn_open ..).2
  iexists ispS, crtS, c1S, isp, msR, pvtR, cfs, M, cu, pm
  iframe # ∗
  ipureintro; exact Hf

end

end Perennial.gryff.replica2
