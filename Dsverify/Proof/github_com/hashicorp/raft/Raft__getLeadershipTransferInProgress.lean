/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__getLeadershipTransferInProgress.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).getLeadershipTransferInProgress`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__getLeadershipTransferInProgress
public import Perennial.Spec.sync.atomic.LoadInt32

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

theorem github_com.hashicorp.raft.Raft.getLeadershipTransferInProgress.wp_proof
    (wp_LoadInt32 : sync.atomic.LoadInt32.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.getLeadershipTransferInProgress.spec (GF := GF) (hG := hG) :=
  fun r γ rc i => by
  wp_start as #Hr
  ihave #Hcells := isRaft_cells r γ rc i $$ Hr
  unfold raftCells ltipCell
  icases Hcells with ⟨-, -, -, -, -, -, #Hltip, -⟩
  wp_auto
  wp_apply (wp_LoadInt32 _ (DFrac.own 1))
  iinv Hltip with ⟨%x, Hv⟩ Hclose
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑ltipN from Iris.Std.LawfulSet.empty_subset)
  iintro Hmask
  inext
  iexists x
  iframe Hv
  iintro Hv
  imod Hmask
  imod Hclose $$ [Hv]
  · inext; iexists x; iframe
  imodintro
  wp_auto
  iapply HΦ; itrivial

end proof

end Perennial
