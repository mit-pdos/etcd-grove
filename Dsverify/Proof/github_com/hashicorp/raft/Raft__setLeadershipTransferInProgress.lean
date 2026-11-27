/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__setLeadershipTransferInProgress.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).setLeadershipTransferInProgress` (stage 2).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setLeadershipTransferInProgress
public import Perennial.Spec.sync.atomic.StoreInt32

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft proto

theorem github_com.hashicorp.raft.Raft.setLeadershipTransferInProgress.wp_proof
    (wp_StoreInt32 : sync.atomic.StoreInt32.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.setLeadershipTransferInProgress.spec (GF := GF) (hG := hG) :=
  fun r γ rc i b => by
  wp_start as #Hr
  ihave #Hcells := isRaft_cells r γ rc i $$ Hr
  unfold raftCells ltipCell
  icases Hcells with ⟨-, -, -, -, -, -, #Hltip, -⟩
  wp_auto
  wp_if_destruct
  all_goals
    wp_apply (wp_StoreInt32 _ _)
    iinv Hltip with ⟨%x, Hv⟩ Hclose
    iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑ltipN from Iris.Std.LawfulSet.empty_subset)
    iintro Hmask
    inext
    iexists x
    iframe Hv
    iintro Hv
    imod Hmask
    imod Hclose $$ [Hv]
    · inext; iexists _; iframe
    imodintro
    wp_auto
    iapply HΦ; itrivial

end proof

end Perennial
