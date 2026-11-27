/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__setLastContact.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).setLastContact`: a write under `lastContactLock` (the writers' guard).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setLastContact
public import Perennial.Proof.sync.Results
public import Perennial.Proof.time.Link

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

theorem github_com.hashicorp.raft.Raft.setLastContact.wp_proof :
    github_com.hashicorp.raft.Raft.setLastContact.spec (GF := GF) (hG := hG) := by
  intro r γ rc i
  wp_start as #His
  ihave #Hl := isRaft_locks r γ rc i $$ His
  unfold raftLocks rwLock
  icases Hl with ⟨-, -, ⟨%γp, #Hguard, -⟩, -⟩
  wp_auto
  wp_apply (sync.RWMutex.wp_Lock_guard _ (lastContactP r)) $$ [] as ⟨Hlk, HP⟩
  · iframe #
  iunfold lastContactP at HP
  icases HP with ⟨%t, Hp⟩
  wp_apply time.wp_Now as %t' _
  wp_apply (sync.RWMutex.wp_Unlock_guard _ (lastContactP r)) $$ [Hlk Hp]
  · iframe Hlk
    inext
    iunfold lastContactP
    iexists t'
    iframe
  iapply HΦ
  itrivial

end proof

end Perennial
