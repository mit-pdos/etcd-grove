/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__LeadershipTransferToServer.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).LeadershipTransferToServer` (stage 2).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__LeadershipTransferToServer
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

theorem github_com.hashicorp.raft.Raft.LeadershipTransferToServer.wp_proof
    (wp_initiate : github_com.hashicorp.raft.Raft.initiateLeadershipTransfer.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.LeadershipTransferToServer.spec (GF := GF) (hG := hG) := by
  intro r γ rc i j
  wp_start as ⟨#Hr, #Hvj⟩
  ihave #Himm := isRaft_imm r γ rc i $$ Hr
  unfold raftImm
  icases Himm with ⟨#Hpv, -⟩
  wp_auto
  ipersist id
  ipersist address
  wp_apply wp_initiate r γ rc i id_ptr address_ptr $$ [$Hr] as %fi Hfi
  · iright; iexists j; iframe #
  iapply HΦ $$ Hfi

end proof

end Perennial
