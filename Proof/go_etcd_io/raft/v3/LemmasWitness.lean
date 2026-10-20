/-
Lemmas of `witness.go`'s proofs (2026-10-20, witness support): the getters of a witness state
held field by field (`whsF`, at any fraction: a handler's own state), of the witness's cache
(`whsOpt`: nil or read-only), and of a witness state's hard state (`hsOptW`), from the getters'
specs.
-/
module

public import Proof.go_etcd_io.raft.v3.InvWitness
public import Spec.go_etcd_io.raft.v3.raftpb.HardState__GetTerm
public import Spec.go_etcd_io.raft.v3.raftpb.HardState__GetVote
public import Spec.go_etcd_io.raft.v3.raftpb.HardState__GetCommit
public import Spec.go_etcd_io.raft.v3.raftpb.WitnessHardState__GetState
public import Spec.go_etcd_io.raft.v3.raftpb.WitnessHardState__GetLastLogIndex
public import Spec.go_etcd_io.raft.v3.raftpb.WitnessHardState__GetLastLogTerm
public import Spec.go_etcd_io.raft.v3.raftpb.WitnessHardState__GetLastLogSubterm
public import Spec.go_etcd_io.raft.v3.raftpb.WitnessHardState__GetLead
public import Spec.go_etcd_io.raft.v3.raftpb.WitnessHardState__GetReplicationSet
public import Spec.go_etcd_io.raft.v3.raftpb.WitnessHardState__GetReplicationSetOutgoing

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `GetState` of a witness state: its hard state. -/
theorem wp_whsF_GetState (wp_GetState : raftpb.WitnessHardState.GetState.spec (GF := GF) (hG := hG))
    (p : Loc) (dq : DFrac) (σ : WHS) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ whsF p dq σ }}
      (App (Val (p @!! go.GoType.PointerType raftpb.WitnessHardState.ty @!! go!"GetState"))
        (Val #()))
    {{ (ps : Loc), RET #ps; hsOptW ps dq σ ∗ (hsOptW ps dq σ -∗ whsF p dq σ) }} := by
  iintro %Φ ⟨#Hi, H⟩ HΦ
  iunfold whsF at H
  iNamed H
  icases whsRest_nn _ _ _ $$ Hr with ⟨%Hnn, Hr⟩
  iapply wp_GetState.1 p dq ps $$ [$Hi $HS]
  · ipureintro; exact Hnn
  inext
  iintro HS
  iapply HΦ
  iframe Hhs
  iintro Hhs
  unfold whsF
  iexists ps
  iframe HS Hhs Hr

theorem wp_whsOpt_GetState (wp_GetState : raftpb.WitnessHardState.GetState.spec (GF := GF) (hG := hG))
    (p : Loc) (σ : WHS) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ whsOpt p σ }}
      (App (Val (p @!! go.GoType.PointerType raftpb.WitnessHardState.ty @!! go!"GetState"))
        (Val #()))
    {{ (ps : Loc), RET #ps; hsOptW ps DFrac.discard σ }} := by
  iintro %Φ ⟨#Hi, #H⟩ HΦ
  iunfold whsOpt at H
  icases H with (⟨%Hp, %Hs⟩ | #H)
  · subst Hp Hs
    iapply wp_GetState.2 $$ Hi
    inext
    iintro -
    iapply HΦ
    unfold hsOptW
    ileft; ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
  · iapply wp_whsF_GetState wp_GetState p DFrac.discard σ $$ [$Hi $H]
    inext
    iintro %ps ⟨#Hhs, -⟩
    iapply HΦ $$ Hhs

theorem wp_hsOptW_GetTerm (wp_GetTerm : raftpb.HardState.GetTerm.spec (GF := GF) (hG := hG))
    (ps : Loc) (dq : DFrac) (σ : WHS) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ hsOptW ps dq σ }}
      (App (Val (ps @!! go.GoType.PointerType raftpb.HardState.ty @!! go!"GetTerm")) (Val #()))
    {{ RET #σ.term; hsOptW ps dq σ }} := by
  iintro %Φ ⟨#Hi, H⟩ HΦ
  unfold hsOptW
  icases H with (%H | H)
  · obtain ⟨Hp, Ht, Hv, Hc⟩ := H
    subst Hp
    iapply wp_GetTerm.2.1 $$ Hi
    inext
    iintro -
    rw [show σ.term = W64 0 by assumption]
    iapply HΦ
    ileft; ipureintro; refine ⟨rfl, ?_, ?_, ?_⟩ <;> first | rfl | assumption
  · iNamed H
    iapply wp_GetTerm.2.2 ps dq _ σ.term $$ [$Hi $HT $cT]
    · ipureintro; exact Hsn
    inext
    iintro HT
    iapply HΦ
    iright
    unfold hsF
    iexists pt, pv, pc, uf
    isplitr
    · ipureintro; exact Hsn
    iframe HT cT HV cV HC cC Hpbs

theorem wp_hsOptW_GetVote (wp_GetVote : raftpb.HardState.GetVote.spec (GF := GF) (hG := hG))
    (ps : Loc) (dq : DFrac) (σ : WHS) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ hsOptW ps dq σ }}
      (App (Val (ps @!! go.GoType.PointerType raftpb.HardState.ty @!! go!"GetVote")) (Val #()))
    {{ RET #σ.vote; hsOptW ps dq σ }} := by
  iintro %Φ ⟨#Hi, H⟩ HΦ
  unfold hsOptW
  icases H with (%H | H)
  · obtain ⟨Hp, Ht, Hv, Hc⟩ := H
    subst Hp
    iapply wp_GetVote.2.1 $$ Hi
    inext
    iintro -
    rw [show σ.vote = W64 0 by assumption]
    iapply HΦ
    ileft; ipureintro; refine ⟨rfl, ?_, ?_, ?_⟩ <;> first | rfl | assumption
  · iNamed H
    iapply wp_GetVote.2.2 ps dq _ σ.vote $$ [$Hi $HV $cV]
    · ipureintro; exact Hsn
    inext
    iintro HV
    iapply HΦ
    iright
    unfold hsF
    iexists pt, pv, pc, uf
    isplitr
    · ipureintro; exact Hsn
    iframe HT cT HV cV HC cC Hpbs

theorem wp_hsOptW_GetCommit (wp_GetCommit : raftpb.HardState.GetCommit.spec (GF := GF) (hG := hG))
    (ps : Loc) (dq : DFrac) (σ : WHS) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ hsOptW ps dq σ }}
      (App (Val (ps @!! go.GoType.PointerType raftpb.HardState.ty @!! go!"GetCommit")) (Val #()))
    {{ RET #σ.commit; hsOptW ps dq σ }} := by
  iintro %Φ ⟨#Hi, H⟩ HΦ
  unfold hsOptW
  icases H with (%H | H)
  · obtain ⟨Hp, Ht, Hv, Hc⟩ := H
    subst Hp
    iapply wp_GetCommit.2.1 $$ Hi
    inext
    iintro -
    rw [show σ.commit = W64 0 by assumption]
    iapply HΦ
    ileft; ipureintro; refine ⟨rfl, ?_, ?_, ?_⟩ <;> first | rfl | assumption
  · iNamed H
    iapply wp_GetCommit.2.2 ps dq _ σ.commit $$ [$Hi $HC $cC]
    · ipureintro; exact Hsn
    inext
    iintro HC
    iapply HΦ
    iright
    unfold hsF
    iexists pt, pv, pc, uf
    isplitr
    · ipureintro; exact Hsn
    iframe HT cT HV cV HC cC Hpbs

theorem wp_whsRest_GetLastLogIndex (wp_GetLastLogIndex : raftpb.WitnessHardState.GetLastLogIndex.spec (GF := GF) (hG := hG))
    (p : Loc) (dq : DFrac) (σ : WHS) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ whsRest p dq σ }}
      (App (Val (p @!! go.GoType.PointerType raftpb.WitnessHardState.ty @!! go!"GetLastLogIndex"))
        (Val #()))
    {{ RET #σ.li; whsRest p dq σ }} := by
  iintro %Φ ⟨#Hi, H⟩ HΦ
  iNamed H
  iapply wp_GetLastLogIndex.1 p dq _ σ.li $$ [$Hi $HLi $cLi]
  · ipureintro; exact Hnn
  inext
  iintro HLi
  iapply HΦ
  unfold whsRest
  iexists pli, plt, pls, pld, srs, sro, uf
  isplitr
  · ipureintro; exact Hnn
  iframe HLi cLi HLt cLt HLs cLs HLd cLd HRs Hrs HRo Hro Hpb

theorem wp_whsOpt_GetLastLogIndex (wp_GetLastLogIndex : raftpb.WitnessHardState.GetLastLogIndex.spec (GF := GF) (hG := hG))
    (p : Loc) (σ : WHS) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ whsOpt p σ }}
      (App (Val (p @!! go.GoType.PointerType raftpb.WitnessHardState.ty @!! go!"GetLastLogIndex"))
        (Val #()))
    {{ RET #σ.li; True }} := by
  iintro %Φ ⟨#Hi, #H⟩ HΦ
  iunfold whsOpt at H
  icases H with (⟨%Hp, %Hs⟩ | #H)
  · subst Hp Hs
    iapply wp_GetLastLogIndex.2 $$ Hi
    inext
    iintro -
    simp only [WHS.zero]
    iapply HΦ; itrivial
  · iunfold whsRO at H
    iunfold whsF at H
    iNamed H
    iapply wp_whsRest_GetLastLogIndex wp_GetLastLogIndex p DFrac.discard σ $$ [$Hi $Hr]
    inext
    iintro -
    iapply HΦ; itrivial

theorem wp_whsRest_GetLastLogTerm (wp_GetLastLogTerm : raftpb.WitnessHardState.GetLastLogTerm.spec (GF := GF) (hG := hG))
    (p : Loc) (dq : DFrac) (σ : WHS) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ whsRest p dq σ }}
      (App (Val (p @!! go.GoType.PointerType raftpb.WitnessHardState.ty @!! go!"GetLastLogTerm"))
        (Val #()))
    {{ RET #σ.lt; whsRest p dq σ }} := by
  iintro %Φ ⟨#Hi, H⟩ HΦ
  iNamed H
  iapply wp_GetLastLogTerm.1 p dq _ σ.lt $$ [$Hi $HLt $cLt]
  · ipureintro; exact Hnn
  inext
  iintro HLt
  iapply HΦ
  unfold whsRest
  iexists pli, plt, pls, pld, srs, sro, uf
  isplitr
  · ipureintro; exact Hnn
  iframe HLi cLi HLt cLt HLs cLs HLd cLd HRs Hrs HRo Hro Hpb

theorem wp_whsOpt_GetLastLogTerm (wp_GetLastLogTerm : raftpb.WitnessHardState.GetLastLogTerm.spec (GF := GF) (hG := hG))
    (p : Loc) (σ : WHS) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ whsOpt p σ }}
      (App (Val (p @!! go.GoType.PointerType raftpb.WitnessHardState.ty @!! go!"GetLastLogTerm"))
        (Val #()))
    {{ RET #σ.lt; True }} := by
  iintro %Φ ⟨#Hi, #H⟩ HΦ
  iunfold whsOpt at H
  icases H with (⟨%Hp, %Hs⟩ | #H)
  · subst Hp Hs
    iapply wp_GetLastLogTerm.2 $$ Hi
    inext
    iintro -
    simp only [WHS.zero]
    iapply HΦ; itrivial
  · iunfold whsRO at H
    iunfold whsF at H
    iNamed H
    iapply wp_whsRest_GetLastLogTerm wp_GetLastLogTerm p DFrac.discard σ $$ [$Hi $Hr]
    inext
    iintro -
    iapply HΦ; itrivial

theorem wp_whsRest_GetLastLogSubterm (wp_GetLastLogSubterm : raftpb.WitnessHardState.GetLastLogSubterm.spec (GF := GF) (hG := hG))
    (p : Loc) (dq : DFrac) (σ : WHS) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ whsRest p dq σ }}
      (App (Val (p @!! go.GoType.PointerType raftpb.WitnessHardState.ty @!! go!"GetLastLogSubterm"))
        (Val #()))
    {{ RET #σ.ls; whsRest p dq σ }} := by
  iintro %Φ ⟨#Hi, H⟩ HΦ
  iNamed H
  iapply wp_GetLastLogSubterm.1 p dq _ σ.ls $$ [$Hi $HLs $cLs]
  · ipureintro; exact Hnn
  inext
  iintro HLs
  iapply HΦ
  unfold whsRest
  iexists pli, plt, pls, pld, srs, sro, uf
  isplitr
  · ipureintro; exact Hnn
  iframe HLi cLi HLt cLt HLs cLs HLd cLd HRs Hrs HRo Hro Hpb

theorem wp_whsOpt_GetLastLogSubterm (wp_GetLastLogSubterm : raftpb.WitnessHardState.GetLastLogSubterm.spec (GF := GF) (hG := hG))
    (p : Loc) (σ : WHS) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ whsOpt p σ }}
      (App (Val (p @!! go.GoType.PointerType raftpb.WitnessHardState.ty @!! go!"GetLastLogSubterm"))
        (Val #()))
    {{ RET #σ.ls; True }} := by
  iintro %Φ ⟨#Hi, #H⟩ HΦ
  iunfold whsOpt at H
  icases H with (⟨%Hp, %Hs⟩ | #H)
  · subst Hp Hs
    iapply wp_GetLastLogSubterm.2 $$ Hi
    inext
    iintro -
    simp only [WHS.zero]
    iapply HΦ; itrivial
  · iunfold whsRO at H
    iunfold whsF at H
    iNamed H
    iapply wp_whsRest_GetLastLogSubterm wp_GetLastLogSubterm p DFrac.discard σ $$ [$Hi $Hr]
    inext
    iintro -
    iapply HΦ; itrivial

theorem wp_whsRest_GetLead (wp_GetLead : raftpb.WitnessHardState.GetLead.spec (GF := GF) (hG := hG))
    (p : Loc) (dq : DFrac) (σ : WHS) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ whsRest p dq σ }}
      (App (Val (p @!! go.GoType.PointerType raftpb.WitnessHardState.ty @!! go!"GetLead"))
        (Val #()))
    {{ RET #σ.lead; whsRest p dq σ }} := by
  iintro %Φ ⟨#Hi, H⟩ HΦ
  iNamed H
  iapply wp_GetLead.1 p dq _ σ.lead $$ [$Hi $HLd $cLd]
  · ipureintro; exact Hnn
  inext
  iintro HLd
  iapply HΦ
  unfold whsRest
  iexists pli, plt, pls, pld, srs, sro, uf
  isplitr
  · ipureintro; exact Hnn
  iframe HLi cLi HLt cLt HLs cLs HLd cLd HRs Hrs HRo Hro Hpb

theorem wp_whsOpt_GetLead (wp_GetLead : raftpb.WitnessHardState.GetLead.spec (GF := GF) (hG := hG))
    (p : Loc) (σ : WHS) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ whsOpt p σ }}
      (App (Val (p @!! go.GoType.PointerType raftpb.WitnessHardState.ty @!! go!"GetLead"))
        (Val #()))
    {{ RET #σ.lead; True }} := by
  iintro %Φ ⟨#Hi, #H⟩ HΦ
  iunfold whsOpt at H
  icases H with (⟨%Hp, %Hs⟩ | #H)
  · subst Hp Hs
    iapply wp_GetLead.2 $$ Hi
    inext
    iintro -
    simp only [WHS.zero]
    iapply HΦ; itrivial
  · iunfold whsRO at H
    iunfold whsF at H
    iNamed H
    iapply wp_whsRest_GetLead wp_GetLead p DFrac.discard σ $$ [$Hi $Hr]
    inext
    iintro -
    iapply HΦ; itrivial


/-- `GetReplicationSet` of a witness state: its read-only slice. -/
theorem wp_whsRest_GetReplicationSet (wp_GetReplicationSet : raftpb.WitnessHardState.GetReplicationSet.spec (GF := GF) (hG := hG))
    (p : Loc) (dq : DFrac) (σ : WHS) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ whsRest p dq σ }}
      (App (Val (p @!! go.GoType.PointerType raftpb.WitnessHardState.ty @!! go!"GetReplicationSet"))
        (Val #()))
    {{ (s : GoSlice), RET #s; s ↦*□ σ.rs ∗ whsRest p dq σ }} := by
  iintro %Φ ⟨#Hi, H⟩ HΦ
  iNamed H
  iapply wp_GetReplicationSet.1 p dq _ $$ [$Hi $HRs]
  · ipureintro; exact Hnn
  inext
  iintro HRs
  iapply HΦ
  iframe Hrs
  unfold whsRest
  iexists pli, plt, pls, pld, srs, sro, uf
  isplitr
  · ipureintro; exact Hnn
  iframe HLi cLi HLt cLt HLs cLs HLd cLd HRs Hrs HRo Hro Hpb

theorem wp_whsOpt_GetReplicationSet (wp_GetReplicationSet : raftpb.WitnessHardState.GetReplicationSet.spec (GF := GF) (hG := hG))
    (p : Loc) (σ : WHS) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ whsOpt p σ }}
      (App (Val (p @!! go.GoType.PointerType raftpb.WitnessHardState.ty @!! go!"GetReplicationSet"))
        (Val #()))
    {{ (s : GoSlice), RET #s; s ↦*□ σ.rs }} := by
  iintro %Φ ⟨#Hi, #H⟩ HΦ
  iunfold whsOpt at H
  icases H with (⟨%Hp, %Hs⟩ | #H)
  · subst Hp Hs
    iapply wp_GetReplicationSet.2 $$ Hi
    inext
    iintro -
    iapply HΦ
    simp only [WHS.zero]
    iapply ownSlice_nil
  · iunfold whsRO at H
    iunfold whsF at H
    iNamed H
    iapply wp_whsRest_GetReplicationSet wp_GetReplicationSet p DFrac.discard σ $$ [$Hi $Hr]
    inext
    iintro %s ⟨#Hs, -⟩
    iapply HΦ $$ Hs

/-- `GetReplicationSetOutgoing` of a witness state: its read-only slice. -/
theorem wp_whsRest_GetReplicationSetOutgoing (wp_GetReplicationSetOutgoing : raftpb.WitnessHardState.GetReplicationSetOutgoing.spec (GF := GF) (hG := hG))
    (p : Loc) (dq : DFrac) (σ : WHS) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ whsRest p dq σ }}
      (App (Val (p @!! go.GoType.PointerType raftpb.WitnessHardState.ty @!! go!"GetReplicationSetOutgoing"))
        (Val #()))
    {{ (s : GoSlice), RET #s; s ↦*□ σ.rsOut ∗ whsRest p dq σ }} := by
  iintro %Φ ⟨#Hi, H⟩ HΦ
  iNamed H
  iapply wp_GetReplicationSetOutgoing.1 p dq _ $$ [$Hi $HRo]
  · ipureintro; exact Hnn
  inext
  iintro HRo
  iapply HΦ
  iframe Hro
  unfold whsRest
  iexists pli, plt, pls, pld, srs, sro, uf
  isplitr
  · ipureintro; exact Hnn
  iframe HLi cLi HLt cLt HLs cLs HLd cLd HRs Hrs HRo Hro Hpb

theorem wp_whsOpt_GetReplicationSetOutgoing (wp_GetReplicationSetOutgoing : raftpb.WitnessHardState.GetReplicationSetOutgoing.spec (GF := GF) (hG := hG))
    (p : Loc) (σ : WHS) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ whsOpt p σ }}
      (App (Val (p @!! go.GoType.PointerType raftpb.WitnessHardState.ty @!! go!"GetReplicationSetOutgoing"))
        (Val #()))
    {{ (s : GoSlice), RET #s; s ↦*□ σ.rsOut }} := by
  iintro %Φ ⟨#Hi, #H⟩ HΦ
  iunfold whsOpt at H
  icases H with (⟨%Hp, %Hs⟩ | #H)
  · subst Hp Hs
    iapply wp_GetReplicationSetOutgoing.2 $$ Hi
    inext
    iintro -
    iapply HΦ
    simp only [WHS.zero]
    iapply ownSlice_nil
  · iunfold whsRO at H
    iunfold whsF at H
    iNamed H
    iapply wp_whsRest_GetReplicationSetOutgoing wp_GetReplicationSetOutgoing p DFrac.discard σ $$ [$Hi $Hr]
    inext
    iintro %s ⟨#Hs, -⟩
    iapply HΦ $$ Hs

end lemmas

end EtcdGrove
end Perennial
