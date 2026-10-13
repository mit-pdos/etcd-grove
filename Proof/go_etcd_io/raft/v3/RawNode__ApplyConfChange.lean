/- Lean-first (no Rocq counterpart), 2026-10-13: reconfiguration stage D. -/
module

public import Spec.go_etcd_io.raft.v3.RawNode__ApplyConfChange
public import Spec.go_etcd_io.raft.v3.raft__applyConfChange
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChange__AsV2
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__AsV2
-- `ownRaftGhost_step_0`
public import Proof.go_etcd_io.raft.v3.Protocol.Facts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open RawNodeOwnAccess

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- After `applyConfChange`: the ghost step its result is (`applyCCOk_step`,
`ownRaftGhost_step_0`), and `ownRawNode` re-sealed at the same client-facing state. -/
private theorem rawNode_applyCC_reseal (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState)
    (s s' : NState) (ps : PState) (rnv : RawNode) (sv : SoftState) (steps : List raftpb.Message)
    (Hrel : NStateRel s ps) (Hin : id ∈ γ.reCfg) (Hasync : rnv.asyncStorageWrites' = false)
    (Hdlen : rs.delivered.length = (uint.Z s.logst.applying).toNat)
    (Hunp : rs.unpersisted = s.logst.unpersisted) (Hsnap : s.logst.snap = none)
    (Hstok : StepsOk s rs.steps) (Htrm : rs.term = s.term) (Hstor : rs.storage = s.logst.storage)
    (Hpvoff : s.prevote = false) (Hrs_out : rs.outlb = s.gh.outlb)
    (Hrs_unst : rs.unst = s.gh.unst) (Hrs_clb : uint.Z rs.clb ≤ uint.Z s.logst.committed)
    (Hok : ApplyCCOk γ.reCfg id s s') :
    ⊢ rawNodeOwn rn rnv -∗ ownRaftPhys γ.reCfg rnv.raft' id s' -∗ ownRaftGhost (GF := GF) γ id ps -∗
      rnv.prevSoftSt' ↦□ sv -∗ rnv.stepsOnAdvance' ↦* steps -∗
      ownSliceCap raftpb.Message rnv.stepsOnAdvance' (DFrac.own 1) -∗
      ([∗list] _k ↦ m;p ∈ steps;rs.steps, pendingRel γ id m p) -∗
      ([∗list] _k ↦ m;p ∈ steps;rs.steps, pendingOwn m p) -∗
      isCommitted γ rs.delivered -∗
      storedRecs γ s.logst.prev s.logst.stored ={⊤}=∗
      ownRawNode γ rn id rs := by
  obtain ⟨Hst, Hro, Hsf, Htk, Htm, Hpv, Hgh, Hls, Hc⟩ := applyCCOk_step _ _ _ _ Hok
  have Hprev : s'.logst.prev = s.logst.prev := by rw [Hls]
  have Hstored : s'.logst.stored = s.logst.stored := by rw [Hls]
  have Happ : s'.logst.applying = s.logst.applying := by rw [Hls]
  have Hunp' : s'.logst.unpersisted = s.logst.unpersisted := by rw [Hls]
  have Hsnap' : s'.logst.snap = s.logst.snap := by rw [Hls]
  have Hstor' : s'.logst.storage = s.logst.storage := by rw [Hls]
  have Hwf' : NStateWf s' := by
    obtain ⟨-, H1, H2⟩ := Hrel
    exact ⟨by rw [Hsf, Hro]; exact H1, by rw [Htk]; exact H2⟩
  iintro Hrn Hphys Hghost #Hsoft Hsteps Hcap #Hpend Hpown #Hdeliv #Hstrecs
  rw [← Hrel.1] at *
  imod ownRaftGhost_step_0 γ id _ _ Hst $$ Hghost with Hghost
  ihave #Hstr' := storedRecs_eq γ _ s'.logst.prev _ s'.logst.stored Hprev Hstored $$ Hstrecs
  iapply ownRawNode_intro γ rn id rs s' (toPState s') rnv sv steps ⟨rfl, Hwf'⟩ Hin Hasync
    (by rw [Happ]; exact Hdlen) (by rw [Hunp']; exact Hunp) (by rw [Hsnap']; exact Hsnap)
    (stepsOk_mono_le s s' _ (by rw [Htm]; exact Int.le_refl _) ⟨Hprev, Hstored⟩ Hc Happ Hpv Hstok)
    (by rw [Htm]; exact Htrm) (by rw [Hstor']; exact Hstor) (by rw [Hpv]; exact Hpvoff)
    (by rw [Hgh]; exact Hrs_out) (by rw [Hgh]; exact Hrs_unst) (Int.le_trans Hrs_clb Hc)
    $$ Hrn Hphys Hghost Hsoft Hsteps Hcap Hpend Hpown Hdeliv Hstr'

theorem RawNode.ApplyConfChange.wp_proof
    (wp_ConfChange_AsV2 : raftpb.ConfChange.AsV2.spec (GF := GF) (hG := hG))
    (wp_ConfChangeV2_AsV2 : raftpb.ConfChangeV2.AsV2.spec (GF := GF) (hG := hG))
    (wp_raft_applyConfChange : raft.applyConfChange.spec (GF := GF) (hG := hG)) :
    RawNode.ApplyConfChange.spec (GF := GF) (hG := hG) := by
  intro γ rn id rs c o dq Hnoop
  wp_start as H
  iNamed H
  iNamed Hrn
  rcases o with m | m
  · -- a `ConfChange`: `AsV2` makes the one change
    simp only [ownCCI, ownCCV1]
    icases Hc with ⟨%v, %Hcv, %Hvm, Hctx⟩
    subst Hcv
    wp_auto
    wp_apply wp_ConfChange_AsV2 as %v2 ⟨%Hv2, Hch⟩
    obtain ⟨Hty, Hnid, Hid⟩ := Hvm
    have Hn : ccApplyM v2.Transition' [({ Type' := v.Type', NodeId' := v.NodeId' } :
        raftpb.ConfChangeSingle)] (cfgState γ.reCfg) = some (cfgState γ.reCfg) := by
      rw [Hv2.1, Hty, Hnid]; exact Hnoop
    wp_apply +noauto wp_raft_applyConfChange γ.reCfg rnv.raft' id s v2 _ (DFrac.own 1) Hin Hn
      $$ [$Hphys $Hch] as %cs %xs %s' ⟨Hphys, -, Hvoters, %Hxs, %Hcs0, %Hok⟩
    imod rawNode_applyCC_reseal γ rn id rs s s' ps rnv sv steps Hrel Hin Hasync Hdlen Hunp Hsnap
      Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hok
      $$ Hrn Hphys Hghost Hsoft Hsteps Hsteps_cap Hpend Hpown Hdeliv Hstrecs with Hrn
    try wp_auto
    iapply HΦ
    simp only [named]
    iframe Hrn Hvoters
    isplitl [Hctx]
    · try simp only [ownCCI, ownCCV1]
      iexists v
      isplitr
      · ipureintro; rfl
      iframe Hctx
      ipureintro; exact ⟨Hty, Hnid, Hid⟩
    iframe
    ipureintro; exact ⟨Hxs, Hcs0⟩
  · -- a `ConfChangeV2`: `AsV2` is itself
    simp only [ownCCI, ownCCV2]
    icases Hc with ⟨%v, %Hcv, %Htr, Hch, Hctx⟩
    subst Hcv
    wp_auto
    wp_apply wp_ConfChangeV2_AsV2
    have Hn : ccApplyM v.Transition' m.changes (cfgState γ.reCfg) = some (cfgState γ.reCfg) := by
      rw [Htr]; exact Hnoop
    wp_apply +noauto wp_raft_applyConfChange γ.reCfg rnv.raft' id s v _ dq Hin Hn
      $$ [$Hphys $Hch] as %cs %xs %s' ⟨Hphys, Hch, Hvoters, %Hxs, %Hcs0, %Hok⟩
    imod rawNode_applyCC_reseal γ rn id rs s s' ps rnv sv steps Hrel Hin Hasync Hdlen Hunp Hsnap
      Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hok
      $$ Hrn Hphys Hghost Hsoft Hsteps Hsteps_cap Hpend Hpown Hdeliv Hstrecs with Hrn
    try wp_auto
    iapply HΦ
    simp only [named]
    iframe Hrn Hvoters
    isplitl [Hch Hctx]
    · try simp only [ownCCI, ownCCV2]
      iexists v
      isplitr
      · ipureintro; rfl
      iframe Hch Hctx
      ipureintro; exact Htr
    iframe
    ipureintro; exact ⟨Hxs, Hcs0⟩

end proof

end EtcdGrove
end Perennial
