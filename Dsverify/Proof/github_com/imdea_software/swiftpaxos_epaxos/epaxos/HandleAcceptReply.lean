/-
`(*Replica).handleAcceptReply` against the model's `hAcceptReply`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.BcastOthers
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.UpdateCommitted
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.PARModel
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.Slot
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.UpdateCommittedP
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.Record
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.BcastKeep
public import Perennial.Proof.time.Results

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model epaxosProof

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [GooseExts]

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : TreemapHyp GF]

/-- What `handleAcceptReply` needs (from the invariant: the reply reaches a bookkeeping,
`Inv.replyTargets`; ids in range, `Inv.msgWf`). -/
structure ARWf (i : Nat) (σ : RState) (ord : List w32) (m : AcceptReply) (w : InstRec)
    (lb : LbRec) : Prop where
  hrep : RepWf i σ ord
  hq : 0 ≤ zz m.replica ∧ zz m.replica < nR
  hn : 0 ≤ zz m.inst ∧ toN m.inst + 1 < MAX_INSTANCE
  hw : σ.inst ⟨toN m.replica, toN m.inst⟩ = some w
  hlb : w.lb = some lb
  hord : ∀ o ∈ ord, 0 ≤ sint.Z o
  houts : OutsWf (hAcceptReply σ m).2

set_option maxHeartbeats 4000000 in
/-- **`handleAcceptReply(areply)`**. -/
theorem wp_handleAcceptReply (hS : replica.Replica.SendMsg.spec (GF := GF))
    (γ : EpNames) (i : Nat) (r rr : Loc) (L : List GoString) (p : FwPtrs) (Rext : IProp GF)
    (ord : List w32) (σ : RState) (l : Loc) (m : AcceptReply) (w : InstRec) (lb : LbRec)
    (hw : ARWf i σ ord m w lb) :
    {{ hdCtx (GF := GF) γ i r rr L p Rext ord ∗ ownRep γ i r σ ∗ ownAcceptReply l m (DFrac.own 1) ∗
        repFrag γ i (hAcceptReply σ m).1 ∗ outsOk γ i (hAcceptReply σ m).2 }}
      (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"handleAcceptReply"))
        (Val #l))
    {{ RET #(); repDone γ i r }} := by
  wp_start as ⟨#Hctx, Hrep, Hm, Hf, Houts⟩
  ihave #Hctx0 := Hctx
  unfold hdCtx
  icases Hctx with ⟨#Hpe, #Hpr, #Hrr, #Hfw, #Hro, #Hinv, #Hpo⟩
  icases ownRep_open γ i r σ $$ Hrep with ⟨%Hib, %Hcb, Hinsts, Hrest⟩
  icases ownRepRest_bump i r σ m.ballot $$ Hrest with ⟨Hmrb, Hrest⟩
  unfold ownAcceptReply
  have hq' : toN m.replica < nR := by
    have := hw.hq.1; have := hw.hq.2; simp only [toN, zz] at *; omega
  have hn' : toN m.inst < MAX_INSTANCE := by have := hw.hn.2; omega
  icases (repInsts_P γ i r σ.inst).1 $$ Hinsts with Hinsts
  icases repInstsP_acc r _ ⟨toN m.replica, toN m.inst⟩ hq' hn' $$ Hinsts with
    ⟨%iss, %rows, %row, %ptrs, %ptr, #Hiss, #Hrows, %Hrow, Hptrs, %Hptr, Hx, Hclose⟩
  ihave Hx := (instAt_some γ i _ ptr w hw.hw).1 $$ Hx
  unfold ownInst
  icases Hx with ⟨%y, Hy, %Hyf, #Hyid, Hycmds, Hydeps, Hylb⟩
  rw [hw.hlb]
  icases Hylb with ⟨%Hlbnn, Hlb⟩
  unfold ownLb
  icases Hlb with ⟨%yl, %gs, %prs, Hyl, %Hylf, Hcp, Hlcmds, Hldeps, Hlprs, %Hlprsl, Hlpr⟩
  ihave %Hrlen := ownSlice_len _ _ _ $$ Hrows
  ihave %Hplen := ownSlice_len _ _ _ $$ Hptrs
  have e1 : sint.Z (W64 (sint.Z m.replica)) = sint.Z m.replica := by word
  have e2 : sint.Z (W64 (sint.Z m.inst)) = sint.Z m.inst := by word
  have hqe : (sint.Z m.replica).toNat = toN m.replica := rfl
  have hne : (sint.Z m.inst).toNat = toN m.inst := rfl
  have h1 : 0 ≤ sint.Z (W64 (sint.Z m.replica)) ∧
      sint.Z (W64 (sint.Z m.replica)) < sint.Z iss.len := by
    have := hw.hq.1; have hl := (List.getElem?_eq_some_iff.mp Hrow).1
    unfold toN zz at *; constructor <;> word
  have h2 : 0 ≤ sint.Z (W64 (sint.Z m.inst)) ∧ sint.Z (W64 (sint.Z m.inst)) < sint.Z row.len := by
    have := hw.hn.1; have := hw.hn.2; have := Hptr.2
    unfold toN zz at *; constructor <;> word
  wp_auto
  simp only [h1, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index iss _ rows _ row h1.1 $$ [$Hrows] as -
  · ipureintro; rw [e1, hqe]; exact Hrow
  simp only [h2, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index row _ ptrs _ ptr h2.1 $$ [$Hptrs] as Hptrs
  · ipureintro; rw [e2, hne]; exact Hptr.1
  ipersist r
  ipersist areply
  wp_join iprop(efld r go!"maxRecvBallot" ↦ (bumpRecvBallot σ m.ballot).maxRecvBallot ∗
      l ↦ epaxos.AcceptReply.mk m.replica m.inst m.ballot) with [Hmrb Hm] as ⟨Hmrb, Hm⟩
  · rw [bumpRecvBallot_true _ _ (by simpa using Hif)]; iframe Hm; iexact Hmrb
  · rw [bumpRecvBallot_false _ _ (by simpa using Hif)]; iframe Hm; iexact Hmrb
  ihave Hrest := Hrest $$ Hmrb
  have hset : ptrs.set (toN m.inst) ptr = ptrs := by
    have := List.getElem?_eq_some_iff.mp Hptr.1
    rw [← this.2]; exact List.set_getElem_self this.1
  rw [Hylf.2.2.2.2.2.2.2.2.1]
  by_cases hs : lb.status = stACCEPTED
  case neg =>
    rw [show decide (lb.status = W8 3) = false from decide_eq_false hs]
    wp_auto
    rw [hAR_ret1 σ m w lb hw.hw hw.hlb (Or.inl hs)]
    iapply HΦ
    iapply repDone_of γ i r _ [] (by intro o ho; simp at ho)
    iframe Hf Houts
    iapply ownRep_of
    iframe Hrest
    isplitr
    · ipureintro; simpa using Hib
    isplitr
    · ipureintro; simpa using Hcb
    ihave Hx := slot_close_gen (GF := GF) γ i ⟨toN m.replica, toN m.inst⟩ ptr y w lb yl gs prs Hyf hw.hlb Hylf
      $$ [Hy Hycmds Hydeps Hyl Hcp Hlcmds Hldeps Hlprs Hlpr]
    · iframe
      isplitl []
      · iexact Hyid
      ipureintro; exact ⟨Hlbnn, Hlprsl⟩
    ihave Hins := Hclose $$ %ptr %(fun pt => instAt γ i ⟨toN m.replica, toN m.inst⟩ pt (some w))
      [Hptrs] Hx
    · rw [hset]; iexact Hptrs
    rw [show updP (instAtP γ i σ.inst) ⟨toN m.replica, toN m.inst⟩
      (fun pt => instAt γ i ⟨toN m.replica, toN m.inst⟩ pt (some w)) = instAtP γ i σ.inst by
        rw [← hw.hw]; exact updP_self _ _]
    simp only [bumpRecvBallot_inst]
    iapply (repInsts_P γ i r σ.inst).2
    iexact Hins
  rw [show decide (lb.status = W8 3) = true from decide_eq_true hs]
  wp_auto
  wp_if_destruct
  · have hc : stGe w.status stCOMMITTED = true :=
      (stGe_iff _ _).mpr (by rw [← Hyf.2.2.1]; exact Hif)
    rw [hAR_ret1 σ m w lb hw.hw hw.hlb (Or.inr hc)]
    iapply HΦ
    iapply repDone_of γ i r _ [] (by intro o ho; simp at ho)
    iframe Hf Houts
    iapply ownRep_of
    iframe Hrest
    isplitr
    · ipureintro; simpa using Hib
    isplitr
    · ipureintro; simpa using Hcb
    ihave Hx := slot_close_gen (GF := GF) γ i ⟨toN m.replica, toN m.inst⟩ ptr y w lb yl gs prs Hyf hw.hlb Hylf
      $$ [Hy Hycmds Hydeps Hyl Hcp Hlcmds Hldeps Hlprs Hlpr]
    · iframe
      isplitl []
      · iexact Hyid
      ipureintro; exact ⟨Hlbnn, Hlprsl⟩
    ihave Hins := Hclose $$ %ptr %(fun pt => instAt γ i ⟨toN m.replica, toN m.inst⟩ pt (some w))
      [Hptrs] Hx
    · rw [hset]; iexact Hptrs
    rw [show updP (instAtP γ i σ.inst) ⟨toN m.replica, toN m.inst⟩
      (fun pt => instAt γ i ⟨toN m.replica, toN m.inst⟩ pt (some w)) = instAtP γ i σ.inst by
        rw [← hw.hw]; exact updP_self _ _]
    simp only [bumpRecvBallot_inst]
    iapply (repInsts_P γ i r σ.inst).2
    iexact Hins
  have h1 : ¬ (lb.status ≠ stACCEPTED ∨ stGe w.status stCOMMITTED = true) := by
    rintro (h | h)
    · exact h hs
    · exact Hif (by rw [Hyf.2.2.1]; exact (stGe_iff _ _).mp h)
  rw [Hylf.2.2.2.2.2.2.2.1]
  wp_if_destruct
  · have hb : lb.lastTriedBallot.slt w.bal = true := by rw [slt_iff, ← Hyf.1]; exact Hif
    rw [hAR_ret2 σ m w lb hw.hw hw.hlb h1 hb]
    iapply HΦ
    iapply repDone_of γ i r _ [] (by intro o ho; simp at ho)
    iframe Hf Houts
    iapply ownRep_of
    iframe Hrest
    isplitr
    · ipureintro; simpa using Hib
    isplitr
    · ipureintro; simpa using Hcb
    ihave Hx := slot_close_gen (GF := GF) γ i ⟨toN m.replica, toN m.inst⟩ ptr y w lb yl gs prs Hyf hw.hlb Hylf
      $$ [Hy Hycmds Hydeps Hyl Hcp Hlcmds Hldeps Hlprs Hlpr]
    · iframe
      isplitl []
      · iexact Hyid
      ipureintro; exact ⟨Hlbnn, Hlprsl⟩
    ihave Hins := Hclose $$ %ptr %(fun pt => instAt γ i ⟨toN m.replica, toN m.inst⟩ pt (some w))
      [Hptrs] Hx
    · rw [hset]; iexact Hptrs
    rw [show updP (instAtP γ i σ.inst) ⟨toN m.replica, toN m.inst⟩
      (fun pt => instAt γ i ⟨toN m.replica, toN m.inst⟩ pt (some w)) = instAtP γ i σ.inst by
        rw [← hw.hw]; exact updP_self _ _]
    simp only [bumpRecvBallot_inst]
    iapply (repInsts_P γ i r σ.inst).2
    iexact Hins
  have hb : lb.lastTriedBallot.slt w.bal = false := by
    rcases h : lb.lastTriedBallot.slt w.bal
    · rfl
    · exact absurd ((slt_iff _ _).mp h) (by rw [← Hyf.1]; exact Hif)
  rw [Hylf.2.2.2.2.2.2.2.1]
  by_cases he : lb.lastTriedBallot = m.ballot
  case neg =>
    rw [show decide (lb.lastTriedBallot = m.ballot) = false from decide_eq_false he]
    wp_auto
    rw [hAR_ret3 σ m w lb hw.hw hw.hlb h1 hb he]
    iapply HΦ
    iapply repDone_of γ i r _ [] (by intro o ho; simp at ho)
    iframe Hf Houts
    iapply ownRep_of
    iframe Hrest
    isplitr
    · ipureintro; simpa using Hib
    isplitr
    · ipureintro; simpa using Hcb
    ihave Hx := slot_close_gen (GF := GF) γ i ⟨toN m.replica, toN m.inst⟩ ptr y w lb yl gs prs Hyf hw.hlb Hylf
      $$ [Hy Hycmds Hydeps Hyl Hcp Hlcmds Hldeps Hlprs Hlpr]
    · iframe
      isplitl []
      · iexact Hyid
      ipureintro; exact ⟨Hlbnn, Hlprsl⟩
    ihave Hins := Hclose $$ %ptr %(fun pt => instAt γ i ⟨toN m.replica, toN m.inst⟩ pt (some w))
      [Hptrs] Hx
    · rw [hset]; iexact Hptrs
    rw [show updP (instAtP γ i σ.inst) ⟨toN m.replica, toN m.inst⟩
      (fun pt => instAt γ i ⟨toN m.replica, toN m.inst⟩ pt (some w)) = instAtP γ i σ.inst by
        rw [← hw.hw]; exact updP_self _ _]
    simp only [bumpRecvBallot_inst]
    iapply (repInsts_P γ i r σ.inst).2
    iexact Hins
  rw [show decide (lb.lastTriedBallot = m.ballot) = true from decide_eq_true he]
  wp_auto
  rw [Hylf.2.2.2.2.2.2.2.1, ← he, show decide (sint.Z lb.lastTriedBallot < sint.Z lb.lastTriedBallot)
    = false from decide_eq_false (Int.lt_irrefl _)]
  wp_auto
  ihave #Hfro := isReplicaFw_ro _ _ _ _ _ _ $$ Hfw
  ihave ⟨#HN, #HF, #HId, #HSt, #HRPC, #HPC, #HThr, #HEx, #HDr, #HSh, #HStats, #HStm, #HAl, %HLn⟩ :=
    fwRO_fields _ _ _ _ _ $$ Hfro
  wp_auto
  have hL5 : L.length = 5 := HLn.1
  rw [hL5, Hylf.2.2.2.1]
  have hN2 : sint.Z (BitVec.sdiv (W64 ((5 : Nat) : Int)) (W64 2)) = sint.Z (W64 (nR / 2 : Nat)) := rfl
  wp_if_destruct
  · -- a majority: commit
    have hq : (W64 (nR / 2 : Nat)).slt (lb.acceptOKs + 1 + 1) = true := by
      rw [slt_iff]; have h' := Hif; rw [hN2] at h'; exact h'
    unfold epaxos.COMMITTED
    wp_auto
    -- the committed instance, its slot kept known (`ptr`), for `updateCommitted`
    have hxc : ((bumpRecvBallot σ m.ballot).setInst ⟨toN m.replica, toN m.inst⟩ (arInst w lb)).inst
        ⟨toN m.replica, toN m.inst⟩ = some (arInst w lb) := by simp [RState.setInst, upd]
    have hnex : w.status ≠ stEXECUTED := fun hex => h1 (Or.inr (by rw [hex]; decide))
    ihave Hx := slot_close_gen (GF := GF) γ i ⟨toN m.replica, toN m.inst⟩ ptr { y with Status' := W8 4 }
      (arInst w lb) (arLb lb) { yl with acceptOKs' := lb.acceptOKs + W64 1, status' := W8 4 }
      gs prs (by
        obtain ⟨a1, a2, a3, a4, a5⟩ := Hyf
        exact ⟨a1, a2, rfl, a4, fun _ => a5 hnex⟩) rfl (by
        obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := Hylf
        exact ⟨a1, a2, a3, rfl, a5, a6, a7, a8, rfl, a10, a11, a12⟩)
      $$ [Hy Hycmds Hydeps Hyl Hcp Hlcmds Hldeps Hlprs Hlpr]
    · rw [show decide ((arInst w lb).status = stEXECUTED) = false by
          simp [arInst, stCOMMITTED, stEXECUTED],
        show decide (w.status = stEXECUTED) = false from decide_eq_false hnex]
      simp only [arInst, arLb]
      have hdo0 : lbDepsOwned lb = false := by
        simp [lbDepsOwned, hs, stACCEPTED, stPREACCEPTED, stPREACCEPTED_EQ]
      have hdo1 : lbDepsOwned { lb with acceptOKs := lb.acceptOKs + 1, status := stCOMMITTED } =
        false := by simp [lbDepsOwned, stCOMMITTED, stPREACCEPTED, stPREACCEPTED_EQ]
      simp only [hdo0, hdo1, Bool.false_eq_true, ↓reduceIte]
      iframe
      isplitl []
      · iexact Hyid
      ipureintro; exact ⟨Hlbnn, Hlprsl⟩
    ihave Hins := Hclose $$ %ptr %(fun pt => iprop(⌜pt = ptr⌝ ∗
        instAt γ i ⟨toN m.replica, toN m.inst⟩ pt (some (arInst w lb)))) [Hptrs] [Hx]
    · rw [hset]; iexact Hptrs
    · isplitr
      · ipureintro; rfl
      iexact Hx
    rw [updP_instAtP_irrel γ i σ.inst ⟨toN m.replica, toN m.inst⟩ (some (arInst w lb))]
    unfold ownRepRest
    icases Hrest with ⟨Hcrt, Hcut, Heut, Hconf, Hmsk, HmaxSeq, Hlead, Hmrb, Hstore, Hpeer⟩
    have hibc : instBounds ((bumpRecvBallot σ m.ballot).setInst ⟨toN m.replica, toN m.inst⟩
        (arInst w lb)).inst := by
      simpa [RState.setInst] using instBounds_upd _ _ _ Hib hq' hw.hn.2
    have hcbc : cutBounds ((bumpRecvBallot σ m.ballot).setInst ⟨toN m.replica, toN m.inst⟩
        (arInst w lb)).committedUpTo := by simpa [RState.setInst] using Hcb
    wp_apply (wp_updateCommittedP γ i r rr L p Rext
      ((bumpRecvBallot σ m.ballot).setInst ⟨toN m.replica, toN m.inst⟩ (arInst w lb)) m.replica
      hw.hq hibc hcbc _ (ptrSlot_status γ i _ ⟨toN m.replica, toN m.inst⟩ ptr (arInst w lb) hxc))
      $$ [$Hrr $Hfw Hins Hcut] as ⟨Hins, Hcut⟩
    · simp only [RState.setInst, bumpRecvBallot_inst, bumpRecvBallot_cut]
      iframe Hins Hcut
    ihave #Hdur := isReplicaFw_durable _ _ _ _ _ _ $$ Hfw
    wp_apply wp_recordInstanceMetadata $$ [$Hrr $Hdur]
    wp_apply wp_sync_e $$ [$Hrr $Hdur]
    -- `inst.lb.clientProposals != nil && !r.Dreply`: the slot read again
    icases repInstsP_acc r _ ⟨toN m.replica, toN m.inst⟩ hq' hn' $$ Hins with
      ⟨%iss2, %rows2, %row2, %ptrs2, %ptr2, #Hiss2, #Hrows2, %Hrow2, Hptrs2, %Hptr2, Hx2, Hclose2⟩
    ihave Hx2 := updP_apply_self _ _ _ _ $$ Hx2
    icases Hx2 with ⟨%He2, Hx2⟩
    subst He2
    ihave Hx2 := (instAt_some γ i _ ptr2 _ rfl).1 $$ Hx2
    unfold ownInst
    icases Hx2 with ⟨%y2, Hy2, %Hyf2, #Hyid2, Hycmds2, Hydeps2, Hylb2⟩
    simp only [arInst]
    icases Hylb2 with ⟨%Hlbnn2, Hlb2⟩
    unfold ownLb
    icases Hlb2 with ⟨%yl2, %gs2, %prs2, Hyl2, %Hylf2, Hcp2, Hlcmds2, Hldeps2, Hlprs2, %Hlprsl2, Hlpr2⟩
    wp_auto
    generalize decide (yl2.clientProposals' = slice.nil) = bnil
    cases bnil <;> wp_auto
    all_goals
      ihave Hx2 := slot_close_gen (GF := GF) γ i ⟨toN m.replica, toN m.inst⟩ ptr2 y2 (arInst w lb) (arLb lb) yl2
        gs2 prs2 Hyf2 rfl Hylf2 $$ [Hy2 Hycmds2 Hydeps2 Hyl2 Hcp2 Hlcmds2 Hldeps2 Hlprs2 Hlpr2]
      · simp only [arInst, arLb]
        iframe
        isplitl []
        · iexact Hyid2
        ipureintro; exact ⟨Hlbnn2, Hlprsl2⟩
      ihave Hins := Hclose2 $$ %ptr2 %(ptrQ γ i ⟨toN m.replica, toN m.inst⟩ ptr2 (arInst w lb))
        [Hptrs2] [Hx2]
      · have hset2 : ptrs2.set (toN m.inst) ptr2 = ptrs2 := by
          have := List.getElem?_eq_some_iff.mp Hptr2.1
          rw [← this.2]; exact List.set_getElem_self this.1
        rw [hset2]; iexact Hptrs2
      · unfold ptrQ; isplitr
        · ipureintro; rfl
        iexact Hx2
      rw [updP_updP]
      have hcom := hAR_commit σ m w lb hw.hw hw.hlb h1 hb he hq
      have houts := hw.houts
      rw [hcom] at houts
      have hm := houts _ (List.mem_cons_of_mem _ List.mem_cons_self)
      rw [hcom]
      rw [← he] at hm ⊢
      ihave ⟨Hob, Hpd, Hcur⟩ := outsOk_bcast1 γ i _ _ (noSends_ev [_]) $$ Houts
      have hwf' : RepWf i (updateCommitted ((bumpRecvBallot σ lb.lastTriedBallot).setInst
          ⟨toN m.replica, toN m.inst⟩ (arInst w lb)) (toN m.replica)) ord :=
        ⟨by simp [updateCommitted, RState.setInst, hw.hrep.id], hw.hrep.hi,
          by simp [updateCommitted, RState.setInst, hw.hrep.po]⟩
      wp_apply (wp_bcastCommitKeep hS γ i r rr L p Rext ord _ m.replica m.inst (arInst w lb) (arLb lb)
        ptr2 hwf' hw.hq hw.hn (by simpa [updateCommitted] using hxc) rfl
        (by simp [lbDepsOwned, arLb, stCOMMITTED, stPREACCEPTED, stPREACCEPTED_EQ]) hm hw.hord)
        $$ [Hins Hcrt Heut Hconf Hmsk HmaxSeq Hlead Hmrb Hstore Hpeer Hcut Hf Hpd Hob]
      · isplitl []
        · unfold hdCtx; iexact Hctx0
        isplitr
        · ipureintro; simpa [updateCommitted, RState.setInst] using instBounds_upd _ _ _ Hib hq' hw.hn.2
        isplitr
        · ipureintro
          rw [← he] at hibc hcbc; exact cutBounds_updateCommitted _ _ hibc hcbc
        rw [show (updateCommitted ((bumpRecvBallot σ lb.lastTriedBallot).setInst
            ⟨toN m.replica, toN m.inst⟩ (arInst w lb)) (toN m.replica)).inst =
            upd σ.inst ⟨toN m.replica, toN m.inst⟩ (some (arInst w lb)) by
          simp [updateCommitted, RState.setInst]]
        rw [ownRepRest_updC]
        simp only [RState.setInst, bumpRecvBallot_inst, arInst]
        iframe
      iintro ⟨Hins, Hrest, Hf, Hpd, Hob⟩
      ihave #Hlock := isReplicaFw_lock _ _ _ _ _ _ $$ Hfw
      wp_auto
      wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, HR⟩
      icases repInstsP_acc r _ ⟨toN m.replica, toN m.inst⟩ hq' hn' $$ Hins with
        ⟨%iss3, %rows3, %row3, %ptrs3, %ptr3, #Hiss3, #Hrows3, %Hrow3, Hptrs3, %Hptr3, Hx3, Hclose3⟩
      ihave Hx3 := updP_apply_self _ _ _ _ $$ Hx3
      unfold ptrQ
      icases Hx3 with ⟨%He3, Hx3⟩
      subst He3
      ihave Hx3 := (instAt_some γ i _ ptr3 _ rfl).1 $$ Hx3
      unfold ownInst
      icases Hx3 with ⟨%y3, Hy3, %Hyf3, Hrest3⟩
      wp_auto
      unfold fwLockInv
      icases HR with ⟨Hcore, Hext⟩
      generalize decide (y3.proposeTime' = W64 0) = bz
      cases bz
      · icases fwCore_stats _ _ _ _ $$ Hcore with ⟨%sm, Hsm, Hcl⟩
        ihave #HStm2 := HStm
        iStructNamed HStm2
        wp_auto
        wp_apply wp_map_lookup1 $$ [$Hsm] as Hsm
        wp_apply time.wp_Now as %tnow -
        wp_apply time.Time.wp_UnixNano' as %ns -
        wp_apply wp_mapInsert $$ [$Hsm] as Hsm
        ihave Hcore := Hcl $$ Hsm
        wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked Hcore Hext]
        · iframe Hcore Hext
        ihave Hx3 : instAt γ i ⟨toN m.replica, toN m.inst⟩ ptr3 (some (arInst w lb)) $$ [Hy3 Hrest3]
        · iapply (instAt_some γ i _ ptr3 _ rfl).2
          unfold ownInst
          iexists y3
          iframe Hy3 Hrest3
          ipureintro; exact Hyf3
        have hset3 : ptrs3.set (toN m.inst) ptr3 = ptrs3 := by
          have := List.getElem?_eq_some_iff.mp Hptr3.1
          rw [← this.2]; exact List.set_getElem_self this.1
        ihave Hins := Hclose3 $$ %ptr3 %(fun pt => instAt γ i ⟨toN m.replica, toN m.inst⟩ pt (some (arInst w lb)))
          [Hptrs3] Hx3
        · rw [hset3]; iexact Hptrs3
        rw [updP_updP, updP_instAtP, upd_self _ _ _ (by simpa [updateCommitted] using hxc)]
        iapply HΦ
        unfold repDone
        iexists _
        iframe Hf
        isplitl [Hins Hrest]
        · iapply ownRep_of
          iframe Hrest
          isplitr
          · ipureintro; rw [← he] at hibc; simpa [updateCommitted] using hibc
          isplitr
          · ipureintro; rw [← he] at hibc hcbc; exact cutBounds_updateCommitted _ _ hibc hcbc
          iapply (repInsts_P γ i r _).2
          iexact Hins
        unfold repIdle outboxesNil; iframe Hob Hpd Hcur
      · wp_auto
        wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked Hcore Hext]
        · iframe Hcore Hext
        ihave Hx3 : instAt γ i ⟨toN m.replica, toN m.inst⟩ ptr3 (some (arInst w lb)) $$ [Hy3 Hrest3]
        · iapply (instAt_some γ i _ ptr3 _ rfl).2
          unfold ownInst
          iexists y3
          iframe Hy3 Hrest3
          ipureintro; exact Hyf3
        have hset3 : ptrs3.set (toN m.inst) ptr3 = ptrs3 := by
          have := List.getElem?_eq_some_iff.mp Hptr3.1
          rw [← this.2]; exact List.set_getElem_self this.1
        ihave Hins := Hclose3 $$ %ptr3 %(fun pt => instAt γ i ⟨toN m.replica, toN m.inst⟩ pt (some (arInst w lb)))
          [Hptrs3] Hx3
        · rw [hset3]; iexact Hptrs3
        rw [updP_updP, updP_instAtP, upd_self _ _ _ (by simpa [updateCommitted] using hxc)]
        iapply HΦ
        unfold repDone
        iexists _
        iframe Hf
        isplitl [Hins Hrest]
        · iapply ownRep_of
          iframe Hrest
          isplitr
          · ipureintro; rw [← he] at hibc; simpa [updateCommitted] using hibc
          isplitr
          · ipureintro; rw [← he] at hibc hcbc; exact cutBounds_updateCommitted _ _ hibc hcbc
          iapply (repInsts_P γ i r _).2
          iexact Hins
        unfold repIdle outboxesNil; iframe Hob Hpd Hcur
  · -- not yet a majority
    have hq : (W64 (nR / 2 : Nat)).slt (lb.acceptOKs + 1 + 1) = false := by
      rcases h : (W64 (nR / 2 : Nat)).slt (lb.acceptOKs + 1 + 1)
      · rfl
      · exact absurd ((slt_iff _ _).mp h) (fun h' => Hif (by rw [hN2]; exact h'))
    rw [hAR_few σ m w lb hw.hw hw.hlb h1 hb he hq]
    rw [← he]
    iapply HΦ
    iapply repDone_of γ i r _ [] (by intro o ho; simp at ho)
    iframe Hf Houts
    iapply ownRep_of
    rw [ownRepRest_setInst]
    iframe Hrest
    isplitr
    · ipureintro; simpa [RState.setInst] using instBounds_upd _ _ _ Hib hq' hw.hn.2
    isplitr
    · ipureintro; simpa [RState.setInst] using Hcb
    ihave Hx := slot_close_gen (GF := GF) γ i ⟨toN m.replica, toN m.inst⟩ ptr y ({ w with lb := some { lb with acceptOKs := lb.acceptOKs + 1 } }) ({ lb with acceptOKs := lb.acceptOKs + 1 }) ({ yl with acceptOKs' := lb.acceptOKs + W64 1 })
      gs prs Hyf rfl (by obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := Hylf; exact ⟨a1, a2, a3, rfl, a5, a6, a7, a8, a9, a10, a11, a12⟩) $$ [Hy Hycmds Hydeps Hyl Hcp Hlcmds Hldeps Hlprs Hlpr]
    · iframe
      isplitl []
      · iexact Hyid
      ipureintro; exact ⟨Hlbnn, Hlprsl⟩
    ihave Hins := Hclose $$ %ptr %(fun pt => instAt γ i ⟨toN m.replica, toN m.inst⟩ pt (some ({ w with lb := some { lb with acceptOKs := lb.acceptOKs + 1 } })))
      [Hptrs] Hx
    · rw [hset]; iexact Hptrs
    rw [updP_instAtP]
    simp only [RState.setInst, bumpRecvBallot_inst]
    iapply (repInsts_P γ i r _).2
    iexact Hins

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
