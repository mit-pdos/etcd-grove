/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H2/InstOpen.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit H2: `epaxosOwn_inst_open` (the interface law whose body is H2's)

`epaxosOwn_inst_open'` proves `Replica2/State.lean`'s `epaxosOwn_inst_open` (same statement): one
slot of the instance space open, with three closings.
-/
module

public import Dsverify.Proof.gryff.H2.EpState

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (RState Copy LB Proposal Msg Ev Out Cmd Deps)
open Perennial.gryff.replica (XS rowOwn nSlots)

attribute [local instance] GooseGlobalGS.gooseInvGS

@[simp] theorem setInst_crtInstance (s : RState) (q i : w32) (c : Copy) :
    (s.setInst q i c).crtInstance = s.crtInstance := rfl
@[simp] theorem setInst_crt (s : RState) (q i : w32) (c : Copy) :
    (s.setInst q i c).crt = s.crt := rfl
@[simp] theorem setInst_confAt (s : RState) (q i : w32) (c : Copy) :
    (s.setInst q i c).confAt = s.confAt := rfl
@[simp] theorem setInst_maxSeqK0 (s : RState) (q i : w32) (c : Copy) :
    (s.setInst q i c).maxSeqK0 = s.maxSeqK0 := rfl

/-- `setInst` at `(q, i)` leaves the other nodes' committedness. -/
theorem committedOrExecuted_setInst (s : RState) (q i : w32) (c : Copy) (n : replica.Node)
    (hn : n ≠ (sint.Z q, sint.Z i)) :
    committedOrExecuted (s.setInst q i c) n = committedOrExecuted s n := by
  unfold committedOrExecuted model.committedCopy
  split
  · rename_i hr
    have hne : ¬(BitVec.ofInt 32 n.1 = q ∧ BitVec.ofInt 32 n.2 = i) := by
      rintro ⟨h1, h2⟩
      apply hn
      have e1 : sint.Z (BitVec.ofInt 32 n.1) = n.1 := by
        unfold model.SLOTS at hr; have := hr.1; have := hr.2.1; word
      have e2 : sint.Z (BitVec.ofInt 32 n.2) = n.2 := by
        unfold model.SLOTS at hr; have := hr.2.2.1; have := hr.2.2.2; word
      rw [← h1, ← h2, e1, e2]
    simp only [model.RState.setInst, hne, ↓reduceIte]
  · rfl

/-- The node of a slot is in its committedness' range. -/
theorem committedOrExecuted_setInst_self (s : RState) (q i : w32) (c : Copy)
    (hb : model.inBox q i = true) :
    committedOrExecuted (s.setInst q i c) (sint.Z q, sint.Z i) =
      (c.status = model.St.COMMITTED ∨ c.status = model.St.EXECUTED) := by
  have hb' := of_decide_eq_true hb
  unfold committedOrExecuted model.committedCopy
  simp only [BitVec.ofInt_toInt, model.RState.setInst, and_self, ↓reduceIte]
  rw [if_pos (by unfold model.SLOTS at hb' ⊢; omega)]
  split <;> simp_all

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]


/-- The pure facts of `epaxosOwn` after `setInst` at an in-box slot whose pointer map entry is
`M'`'s (`p'`), the others unchanged. -/
theorem epFacts_setInst (xs : XS) (s : RState) (isp : List GoSlice) (cfs : List Loc)
    (M M' : GMap replica.Node Loc) (cu : GoArray w32 5) (pm : GMap w64 src.gryffproto.ValTag)
    (q i : w32) (c' : Copy) (p' : Loc) (hb : model.inBox q i = true)
    (Hf : epFacts xs s isp cfs M cu pm)
    (hM' : M'.lookup (sint.Z q, sint.Z i) = some p')
    (hMo : ∀ n, n ≠ (sint.Z q, sint.Z i) → M'.lookup n = M.lookup n)
    (hx : ((sint.Z q, sint.Z i) ∈ xs.1 ∨ xs.numF (sint.Z q, sint.Z i) ≠ 0 ∨
        xs.lowF (sint.Z q, sint.Z i) ≠ 0) →
      committedOrExecuted (s.setInst q i c') (sint.Z q, sint.Z i) = true) :
    epFacts xs (s.setInst q i c') isp cfs M' cu pm := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := Hf
  refine ⟨h1, h2, h3, h4, h5, h6, ?_, ?_, ?_, ?_, h11⟩
  · intro q' i' hb'
    by_cases e : q' = q ∧ i' = i
    · obtain ⟨rfl, rfl⟩ := e
      simp [model.RState.setInst, hM']
    · have hn : ((sint.Z q', sint.Z i') : replica.Node) ≠ (sint.Z q, sint.Z i) :=
        fun h => e ((node_eq_iff q i q' i').1 h)
      simp only [model.RState.setInst, e, ↓reduceIte, hMo _ hn]
      exact h7 q' i' hb'
  · intro q' i' hb'
    have e : ¬(q' = q ∧ i' = i) := by rintro ⟨rfl, rfl⟩; rw [hb] at hb'; cases hb'
    simp only [model.RState.setInst, e, ↓reduceIte]
    exact h8 q' i' hb'
  · intro n hn
    by_cases e : n = (sint.Z q, sint.Z i)
    · subst e; rw [hM']; rfl
    · rw [hMo n e]; exact h9 n hn
  · intro n hn
    by_cases e : n = (sint.Z q, sint.Z i)
    · subst e; exact hx hn
    · rw [committedOrExecuted_setInst s q i c' n e]; exact h10 n hn


/-- An element's ownership follows its node's committedness (persisted when it becomes
committed). -/
theorem elem_upd (ρ : Repl2Names) (n : replica.Node) (p : Loc) (b b' : Bool) (h : b = true → b' = true) :
    (ghostMapElem ρ.ptrs n (if b then DFrac.discard else DFrac.own 1) p : IProp GF) ⊢
      |==> ghostMapElem ρ.ptrs n (if b' then DFrac.discard else DFrac.own 1) p := by
  cases b <;> cases b'
  · iintro H; imodintro; iexact H
  · iintro H; simp only [Bool.false_eq_true, ↓reduceIte]; iapply ghostMapElem_persist $$ H
  · exact absurd (h rfl) (by simp)
  · iintro H; imodintro; iexact H

/-- The elements of the nodes other than `n0` keep their ownership. -/
theorem elems_congr (ρ : Repl2Names) (s s' : RState) (M : GMap replica.Node Loc)
    (n0 : replica.Node) (h : ∀ n, n ≠ n0 → committedOrExecuted s' n = committedOrExecuted s n) :
    ([∗map] n ↦ p ∈ delete M n0, (ghostMapElem ρ.ptrs n
        (if committedOrExecuted s n then DFrac.discard else DFrac.own 1) p : IProp GF)) ⊢
      [∗map] n ↦ p ∈ delete M n0, ghostMapElem ρ.ptrs n
        (if committedOrExecuted s' n then DFrac.discard else DFrac.own 1) p := by
  apply BigSepM.bigSepM_mono
  intro n p hnp
  have hne : n ≠ n0 := by
    intro e; subst e
    rw [LawfulPartialMap.get?_delete_eq rfl] at hnp; cases hnp
  rw [h n hne]

/-- **Replace an instance's pointer and copy**. -/
theorem insts_replace (ρ : Repl2Names) (xs : XS) (s : RState) (M : GMap replica.Node Loc)
    (q i : w32) (p : Loc) (c : Copy) (hM : M.lookup (sint.Z q, sint.Z i) = some p)
    (hs : s.inst q i = some c) :
    instsRep (GF := GF) ρ xs s M ⊢ copyRep ρ xs (sint.Z q, sint.Z i) p c ∗
      ∀ (s' : RState) (p' : Loc) (c' : Copy), ⌜s'.inst q i = some c' ∧
          ∀ q' i', ¬(q' = q ∧ i' = i) → s'.inst q' i' = s.inst q' i'⌝ -∗
        copyRep ρ xs (sint.Z q, sint.Z i) p' c' -∗
        instsRep ρ xs s' (GMap.insert (sint.Z q, sint.Z i) p' M) := by
  unfold instsRep
  iintro H
  icases (BigSepM.bigSepM_delete (show get? M (sint.Z q, sint.Z i) = some p from hM)).1 $$ H
    with ⟨⟨%c0, %Hc0, Hp⟩, Hrest⟩
  simp only [BitVec.ofInt_toInt, hs, Option.some.injEq] at Hc0
  subst Hc0
  iframe Hp
  iintro %s' %p' %c' %Hs' Hp'
  rw [← GMap.insert_delete]
  iapply (BigSepM.bigSepM_insert (show get? (GMap.delete (sint.Z q, sint.Z i) M)
    (sint.Z q, sint.Z i) = none from LawfulPartialMap.get?_delete_eq rfl)).2
  isplitl [Hp']
  · iexists c'
    iframe Hp'
    ipureintro
    simp only [BitVec.ofInt_toInt]; exact Hs'.1
  iapply BigSepM.bigSepM_mono (fun {n p'} hnp => ?_) $$ Hrest
  have hne : n ≠ (sint.Z q, sint.Z i) := by
    intro e; subst e
    rw [LawfulPartialMap.get?_delete_eq rfl] at hnp; cases hnp
  iintro ⟨%c1, %Hc1, Hp1⟩
  ihave %Hn := copyRep_node ρ xs n p' c1 $$ Hp1
  iexists c1
  iframe Hp1
  ipureintro
  rw [Hs'.2]
  · exact Hc1
  · rintro ⟨h1, h2⟩
    apply hne
    rw [Hn, h1, h2]

set_option maxHeartbeats 1000000 in
/-- **`epaxosOwn_inst_open`** (`Replica2/State.lean`), proved. -/
theorem epaxosOwn_inst_open' (ρ : Repl2Names) (h r : Loc) (xs : XS) (s : RState) (q i : w32)
    (hb : model.inBox q i = true) :
    epaxosOwn (GF := GF) ρ h r xs s ⊢ ∃ (ispS sq : GoSlice) (isp : List GoSlice) (ptrs : List Loc) (p : Loc),
      h.[src.gryff.EPaxosRMWHandler, go!"InstanceSpace"] ↦□ ispS ∗ ispS ↦*□ isp ∗
      ⌜isp[(sint.Z q).toNat]? = some sq ∧ ptrs[(sint.Z i).toNat]? = some p⌝ ∗ sq ↦* ptrs ∗
      (match s.inst q i with
       | none => iprop(⌜p = Loc.null⌝)
       | some c => iprop(⌜p ≠ Loc.null⌝ ∗ copyRep ρ xs (sint.Z q, sint.Z i) p c)) ∗
      ⌜committedOrExecuted s (sint.Z q, sint.Z i) = false →
        xs.numF (sint.Z q, sint.Z i) = 0 ∧ xs.lowF (sint.Z q, sint.Z i) = 0 ∧
        (sint.Z q, sint.Z i) ∉ xs.1⌝ ∗
      ((∀ c' : Copy, ⌜(s.inst q i).isSome ∧ (committedOrExecuted s (sint.Z q, sint.Z i) = true →
            committedOrExecuted (s.setInst q i c') (sint.Z q, sint.Z i) = true)⌝ -∗
          sq ↦* ptrs -∗ copyRep ρ xs (sint.Z q, sint.Z i) p c' -∗
          |==> epaxosOwn ρ h r xs (s.setInst q i c')) ∧
       (∀ (p' : Loc) (c' : Copy), ⌜s.inst q i = none ∧ p' ≠ Loc.null⌝ -∗
          sq ↦* ptrs.set (sint.Z i).toNat p' -∗ copyRep ρ xs (sint.Z q, sint.Z i) p' c' -∗
          |==> epaxosOwn ρ h r xs (s.setInst q i c')) ∧
       (∀ (p' : Loc) (c' : Copy), ⌜(s.inst q i).isSome ∧
            committedOrExecuted s (sint.Z q, sint.Z i) = false ∧ p' ≠ Loc.null⌝ -∗
          sq ↦* ptrs.set (sint.Z i).toNat p' -∗ copyRep ρ xs (sint.Z q, sint.Z i) p' c' -∗
          |==> epaxosOwn ρ h r xs (s.setInst q i c'))) := by
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
  -- the closing of the rows, given row `q`'s new pointers
  have hrowsM : ∀ (M' : GMap replica.Node Loc), (∀ k j : Nat, k ≠ (sint.Z q).toNat →
      M'.lookup ((k : Int), (j : Int)) = M.lookup ((k : Int), (j : Int))) → True := fun _ _ => trivial
  iexists ispS, sq, isp, ptrs, p
  isplitr; · iexact HispS
  isplitr; · iexact Hisp
  isplitr; · ipureintro; exact ⟨hsq, hp⟩
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
    isplit
    · iintro %c' %hc'; simp at hc'
    isplit
    · iintro %p' %c' %hc' Hrow Hc'
      imod ghost_map_insert (γ := ρ.ptrs) (sint.Z q, sint.Z i) p' hMn $$ HM with ⟨HM, Hel⟩
      ihave >Hel := elem_upd ρ (sint.Z q, sint.Z i) p' false
        (committedOrExecuted (s.setInst q i c') (sint.Z q, sint.Z i)) (by simp) $$ [Hel]
      · simp only [Bool.false_eq_true, ↓reduceIte]; iexact Hel
      ihave Hrow := rowOwn_insert M _ _ sq ptrs p' hc'.2 Hrowf.1 Hrowf.2 $$ Hrow
      simp only [hqN, hiN]
      ihave Hrows := Hrows $$ %(GMap.insert (sint.Z q, sint.Z i) p' M) %?_ Hrow
      · intro k j hk
        rw [GMap.lookup_insert_ne _ _ (by intro e; simp only [Prod.mk.injEq] at e; omega)]
      ihave Hinsts := insts_insert ρ xs s (s.setInst q i c') M q i p' c' hMn
        (by simp [model.RState.setInst])
        (fun q' i' hne => by simp only [model.RState.setInst, hne, ↓reduceIte]) $$ [$Hinsts $Hc']
      imodintro
      iapply (epaxosOwn_open ..).2
      iexists ispS, crtS, c1S, isp, msR, pvtR, cfs, (GMap.insert (sint.Z q, sint.Z i) p' M), cu, pm
      simp only [setInst_crtInstance, setInst_crt, setInst_confAt, setInst_maxSeqK0]
      iframe # ∗
      isplitl [HMe Hel]
      · iapply (BigSepM.bigSepM_insert (show get? M (sint.Z q, sint.Z i) = none from hMn)).2
        iframe Hel
        iapply BigSepM.bigSepM_mono (fun {n p0} hnp => ?_) $$ HMe
        have hne : n ≠ (sint.Z q, sint.Z i) := by
          intro e; subst e; rw [show get? M (sint.Z q, sint.Z i) = none from hMn] at hnp; cases hnp
        rw [committedOrExecuted_setInst s q i c' n hne]
      · ipureintro
        exact epFacts_setInst xs s isp cfs M _ cu pm q i c' p' hb Hf (GMap.lookup_insert ..)
          (fun n hn => GMap.lookup_insert_ne _ _ (Ne.symm hn))
          (fun hx => by have := Hf.2.2.2.2.2.2.2.2.1 _ hx; rw [hMn] at this; cases this)
    · iintro %p' %c' %hc'; simp at hc'
  · -- a copy
    have hpn : p ≠ Loc.null := by
      intro e; rw [e] at hMp; simp only [↓reduceIte] at hMp; rw [hsi, hMp] at hinst
      simp at hinst
    have hMs : M.lookup (sint.Z q, sint.Z i) = some p := by
      rw [hMp]; simp [hpn]
    icases insts_replace ρ xs s M q i p c hMs hsi $$ Hinsts with ⟨Hc, Hclose⟩
    dsimp only
    isplitl [Hc]
    · iframe Hc; ipureintro; exact hpn
    isplitr; · ipureintro; exact hxs
    icases (BigSepM.bigSepM_delete (show get? M (sint.Z q, sint.Z i) = some p from hMs)).1 $$ HMe
      with ⟨Hel, HMe⟩
    isplit
    · -- (a) the same pointer
      iintro %c' %hc' Hrow Hc'
      ihave >Hel := elem_upd ρ (sint.Z q, sint.Z i) p _ _ hc'.2 $$ Hel
      ihave Hrow := (replica.rowOwn_open M _ sq).2 $$ [Hrow]
      · iexists ptrs; iframe; ipureintro; exact Hrowf
      ihave Hrows := Hrows $$ %M %(fun _ _ _ => rfl) Hrow
      have hsc : (s.setInst q i c').inst q i = some c' ∧ ∀ q' i', ¬(q' = q ∧ i' = i) →
          (s.setInst q i c').inst q' i' = s.inst q' i' :=
        ⟨by simp [model.RState.setInst],
          fun q' i' hne => by simp only [model.RState.setInst, hne, ↓reduceIte]⟩
      ihave Hinsts := Hclose $$ %(s.setInst q i c') %p %c' %hsc Hc'
      rw [GMap.insert_id M _ p hMs]
      imodintro
      iapply (epaxosOwn_open ..).2
      iexists ispS, crtS, c1S, isp, msR, pvtR, cfs, M, cu, pm
      simp only [setInst_crtInstance, setInst_crt, setInst_confAt, setInst_maxSeqK0]
      iframe # ∗
      isplitl [HMe Hel]
      · iapply (BigSepM.bigSepM_delete (show get? M (sint.Z q, sint.Z i) = some p from hMs)).2
        iframe Hel
        iapply elems_congr ρ s (s.setInst q i c') M _
          (fun n hn => committedOrExecuted_setInst s q i c' n hn) $$ HMe
      · ipureintro
        exact epFacts_setInst xs s isp cfs M M cu pm q i c' p hb Hf hMs (fun _ _ => rfl)
          (fun hx => hc'.2 (Hf.2.2.2.2.2.2.2.2.2.1 _ hx))
    isplit
    · iintro %p' %c' %hc'; simp [hsi] at hc'
    · -- (c) a fresh pointer replacing an uncommitted copy's
      iintro %p' %c' %hc' Hrow Hc'
      simp only [hc'.2.1, Bool.false_eq_true, ↓reduceIte]
      imod ghost_map_update (γ := ρ.ptrs) p' $$ HM Hel with ⟨HM, Hel⟩
      ihave >Hel := elem_upd ρ (sint.Z q, sint.Z i) p' false
        (committedOrExecuted (s.setInst q i c') (sint.Z q, sint.Z i)) (by simp) $$ [Hel]
      · simp only [Bool.false_eq_true, ↓reduceIte]; iexact Hel
      ihave Hrow := rowOwn_insert M _ _ sq ptrs p' hc'.2.2 Hrowf.1 Hrowf.2 $$ Hrow
      simp only [hqN, hiN]
      ihave Hrows := Hrows $$ %(GMap.insert (sint.Z q, sint.Z i) p' M) %?_ Hrow
      · intro k j hk
        rw [GMap.lookup_insert_ne _ _ (by intro e; simp only [Prod.mk.injEq] at e; omega)]
      have hsc : (s.setInst q i c').inst q i = some c' ∧ ∀ q' i', ¬(q' = q ∧ i' = i) →
          (s.setInst q i c').inst q' i' = s.inst q' i' :=
        ⟨by simp [model.RState.setInst],
          fun q' i' hne => by simp only [model.RState.setInst, hne, ↓reduceIte]⟩
      ihave Hinsts := Hclose $$ %(s.setInst q i c') %p' %c' %hsc Hc'
      imodintro
      iapply (epaxosOwn_open ..).2
      iexists ispS, crtS, c1S, isp, msR, pvtR, cfs, (GMap.insert (sint.Z q, sint.Z i) p' M), cu, pm
      simp only [setInst_crtInstance, setInst_crt, setInst_confAt, setInst_maxSeqK0]
      iframe # ∗
      isplitl [HMe Hel]
      · rw [← GMap.insert_delete]
        iapply (BigSepM.bigSepM_insert (show get? (delete M (sint.Z q, sint.Z i))
          (sint.Z q, sint.Z i) = none from LawfulPartialMap.get?_delete_eq rfl)).2
        iframe Hel
        iapply elems_congr ρ s (s.setInst q i c') M _
          (fun n hn => committedOrExecuted_setInst s q i c' n hn) $$ HMe
      · ipureintro
        exact epFacts_setInst xs s isp cfs M _ cu pm q i c' p' hb Hf (GMap.lookup_insert ..)
          (fun n hn => GMap.lookup_insert_ne _ _ (Ne.symm hn))
          (fun hx => absurd (Hf.2.2.2.2.2.2.2.2.2.1 _ hx) (by rw [hc'.2.1]; simp))

end

end Perennial.gryff.replica2

