/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__replicateTo.lean (241f27e).
-/
/-
The proof of `Raft__replicateTo` (replication subsystem).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__replicateTo
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setupAppendEntries
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__sendLatestSnapshot
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getCurrentTerm
public import Dsverify.Spec.github_com.hashicorp.raft.appendStats
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__handleStaleTerm
public import Dsverify.Spec.github_com.hashicorp.raft.followerReplication__setLastContact
public import Dsverify.Spec.github_com.hashicorp.raft.updateLastAppended
public import Dsverify.Proof.github_com.hashicorp.raft.ReplNotify
public import Dsverify.Spec.github_com.hashicorp.raft.backoff
public import Dsverify.Spec.github_com.hashicorp.raft.min
public import Dsverify.Spec.github_com.hashicorp.raft.max
public import Perennial.Spec.time.Now
public import Perennial.Spec.time.After

@[expose] public section

set_option linter.unusedVariables false
set_option linter.deprecated false

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

theorem github_com.hashicorp.raft.Raft.replicateTo.wp_proof
    (wp_LoadUint64 : sync.atomic.LoadUint64.spec (GF := GF) (hG := hG))
    (wp_StoreUint64 : sync.atomic.StoreUint64.spec (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG))
    (wp_After : time.After.spec (GF := GF) (hG := hG))
    (wp_setupAppendEntries : github_com.hashicorp.raft.Raft.setupAppendEntries.spec (GF := GF) (hG := hG))
    (wp_sendLatestSnapshot : github_com.hashicorp.raft.Raft.sendLatestSnapshot.spec (GF := GF) (hG := hG))
    (wp_getCurrentTerm : github_com.hashicorp.raft.raftState.getCurrentTerm.spec (GF := GF) (hG := hG))
    (wp_appendStats : github_com.hashicorp.raft.appendStats.spec (GF := GF) (hG := hG))
    (wp_handleStaleTerm : github_com.hashicorp.raft.Raft.handleStaleTerm.spec (GF := GF) (hG := hG))
    (wp_setLastContact : github_com.hashicorp.raft.followerReplication.setLastContact.spec (GF := GF) (hG := hG))
    (wp_updateLastAppended : github_com.hashicorp.raft.updateLastAppended.spec (GF := GF) (hG := hG))
    (wp_backoff : github_com.hashicorp.raft.backoff.spec (GF := GF) (hG := hG))
    (wp_min : github_com.hashicorp.raft.min.spec (GF := GF) (hG := hG))
    (wp_max : github_com.hashicorp.raft.max.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.replicateTo.spec (GF := GF) (hG := hG) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

end proof

end Perennial
