/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__appendConfigurationEntry.lean (241f27e).
-/
/-
The proof of `raft.Raft.appendConfigurationEntry` (stage 4).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__appendConfigurationEntry
public import Dsverify.Spec.github_com.hashicorp.raft.nextConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.EncodeConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setLatestConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.commitment__setConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__startStopReplication
public import Dsverify.Spec.github_com.hashicorp.raft.deferError__respond
public import Dsverify.Proof.github_com.hashicorp.raft.leader.Dispatch
public import Dsverify.Proof.github_com.hashicorp.raft.leader.Ccf

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
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

open github_com.hashicorp.raft github_com.hashicorp.raft.gprot github_com.hashicorp.raft.proto

theorem github_com.hashicorp.raft.Raft.appendConfigurationEntry.wp_proof
    (wp_nextConfiguration : github_com.hashicorp.raft.nextConfiguration.spec (GF := GF) (hG := hG))
    (wp_EncodeConfiguration : github_com.hashicorp.raft.EncodeConfiguration.spec (GF := GF) (hG := hG))
    (wp_getCurrentTerm : github_com.hashicorp.raft.raftState.getCurrentTerm.spec (GF := GF) (hG := hG))
    (wp_getLastIndex : github_com.hashicorp.raft.raftState.getLastIndex.spec (GF := GF) (hG := hG))
    (wp_getCommitIndex : github_com.hashicorp.raft.raftState.getCommitIndex.spec (GF := GF) (hG := hG))
    (wp_tryStageCommitIndex : github_com.hashicorp.raft.Raft.tryStageCommitIndex.spec (GF := GF) (hG := hG))
    (wp_match : github_com.hashicorp.raft.commitment.match.spec (GF := GF) (hG := hG))
    (wp_setLastLog : github_com.hashicorp.raft.raftState.setLastLog.spec (GF := GF) (hG := hG))
    (wp_asyncNotifyCh : github_com.hashicorp.raft.asyncNotifyCh.spec (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG))
    (wp_setLatestConfiguration : github_com.hashicorp.raft.Raft.setLatestConfiguration.spec (GF := GF) (hG := hG))
    (wp_setConfiguration : github_com.hashicorp.raft.commitment.setConfiguration.spec (GF := GF) (hG := hG))
    (wp_startStopReplication : github_com.hashicorp.raft.Raft.startStopReplication.spec (GF := GF) (hG := hG))
    (wp_respond : github_com.hashicorp.raft.deferError.respond.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.appendConfigurationEntry.spec (GF := GF) (hG := hG) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

end proof

end Perennial
