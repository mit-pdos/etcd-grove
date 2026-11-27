/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__handleStaleTerm.lean (241f27e).
-/
/-
The proof of `Raft__handleStaleTerm` (replication subsystem).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__handleStaleTerm
public import Dsverify.Spec.github_com.hashicorp.raft.followerReplication__notifyAll
public import Dsverify.Spec.github_com.hashicorp.raft.asyncNotifyCh

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

open github_com.hashicorp.raft github_com.hashicorp.raft.gprot proto

theorem github_com.hashicorp.raft.Raft.handleStaleTerm.wp_proof
    (wp_notifyAll : github_com.hashicorp.raft.followerReplication.notifyAll.spec (GF := GF) (hG := hG))
    (wp_asyncNotifyCh : github_com.hashicorp.raft.asyncNotifyCh.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.handleStaleTerm.spec (GF := GF) (hG := hG) :=
  fun r γ rc i T j s => by
  wp_start as ⟨#Hr, #Hs⟩
  wp_auto
  wp_apply wp_notifyAll $$ [$Hr $Hs]
  · ipureintro; rfl
  ihave ⟨-, -, -, -, -, -, -, ⟨%sd, #Hsd, #Hsdc⟩, -⟩ := replShared_core r γ i T j s $$ Hs
  unfold notifyChan
  icases Hsdc with ⟨%γc, #Hbag⟩
  wp_auto
  wp_apply wp_asyncNotifyCh $$ [$Hbag]
  iapply HΦ; itrivial

end proof

end Perennial
