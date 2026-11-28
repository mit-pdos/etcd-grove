/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/followerReplication__LastContact.lean (241f27e).
-/
/-
The proof of `followerReplication__LastContact` (replication subsystem).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.followerReplication__LastContact
public import Dsverify.Proof.github_com.hashicorp.raft.ReplNotify
public import Dsverify.Proof.github_com.hashicorp.raft.ReplBase

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

theorem github_com.hashicorp.raft.followerReplication.LastContact.wp_proof :
    github_com.hashicorp.raft.followerReplication.LastContact.spec (GF := GF) (hG := hG) :=
  fun r γ rc i T j s tid => by
  wp_start as ⟨#Hs, Htok⟩
  ihave #Hlcl := replShared_contact r γ rc i T j s $$ Hs
  unfold rwLock
  icases Hlcl with ⟨%γp, #Hguard, #Hpool⟩
  iapply wp_fupd
  wp_auto_lc 1
  imod qpool.borrow_lc replContactLockN γp _ ⊤ (by solve_ndisj) tid $$ [$Hlc1 $Hpool $Htok]
    with ⟨Hown, Hloan⟩
  wp_apply (sync.RWMutex.wp_RLock _ _) $$ [$Hown] as ⟨Hrlocked, HP⟩
  icases HP with ⟨%t0, Ht⟩
  wp_auto
  wp_apply (sync.RWMutex.wp_RUnlock _ _) $$ [$Hrlocked Ht] as Hown
  · iexists t0; iframe
  imod qpool.giveBack replContactLockN γp _ ⊤ (by solve_ndisj) tid $$ [$Hpool $Hloan $Hown]
    with Htok
  imodintro
  iapply HΦ $$ Htok

end proof

end Perennial
