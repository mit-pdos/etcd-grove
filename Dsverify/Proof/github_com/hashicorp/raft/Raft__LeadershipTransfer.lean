/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__LeadershipTransfer.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).LeadershipTransfer` (stage 2).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__LeadershipTransfer
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__initiateLeadershipTransfer

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

open github_com.hashicorp.raft proto gprot

theorem github_com.hashicorp.raft.Raft.LeadershipTransfer.wp_proof
    (wp_initiate : github_com.hashicorp.raft.Raft.initiateLeadershipTransfer.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.LeadershipTransfer.spec (GF := GF) (hG := hG) := by
  intro r γ rc i
  wp_start as #Hr
  ihave #Himm := isRaft_imm r γ rc i $$ Hr
  unfold raftImm
  icases Himm with ⟨#Hpv, -⟩
  wp_auto
  wp_apply wp_initiate r γ rc i null null $$ [$Hr] as %fi Hfi
  · ileft; ipureintro; exact ⟨rfl, rfl⟩
  iapply HΦ $$ Hfi

end proof

end Perennial
