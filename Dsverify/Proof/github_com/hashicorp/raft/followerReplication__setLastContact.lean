/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/followerReplication__setLastContact.lean (241f27e).
-/
/-
The proof of `followerReplication__setLastContact` (replication subsystem).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.followerReplication__setLastContact
public import Dsverify.Proof.github_com.hashicorp.raft.ReplNotify
public import Perennial.Spec.time.Now

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

theorem github_com.hashicorp.raft.followerReplication.setLastContact.wp_proof
    (wp_Now : time.Now.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.followerReplication.setLastContact.spec (GF := GF) (hG := hG) :=
  fun r γ rc i T j s => by
  wp_start as #Hs
  ihave #Hlcl := replShared_contact r γ rc i T j s $$ Hs
  unfold rwLock
  icases Hlcl with ⟨%γp, #Hguard, #Hpool⟩
  wp_auto
  wp_apply (sync.RWMutex.wp_Lock_guard _ _) $$ [$Hguard] as ⟨Hlocked, HP⟩
  wp_apply wp_Now as %t -
  icases HP with ⟨%t0, Ht⟩
  wp_auto
  wp_apply (sync.RWMutex.wp_Unlock_guard _ _) $$ [$Hlocked Ht]
  · iexists t; iframe
  iapply HΦ; itrivial

end proof

end Perennial
