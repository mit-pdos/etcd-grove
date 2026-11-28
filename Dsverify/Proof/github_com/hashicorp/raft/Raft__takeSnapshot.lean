/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__takeSnapshot.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).takeSnapshot` (stage 3): the FSM goroutine's snapshot, the main loop's
configurations, the sink's commit (`snapProof.own_commit`), the last snapshot, the compaction.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__takeSnapshot
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__setLastSnapshot
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__compactLogs
public import Dsverify.Spec.github_com.hashicorp.raft.getSnapshotVersion
public import Dsverify.Proof.github_com.hashicorp.raft.InstallBase
public import Dsverify.Proof.github_com.hashicorp.raft.SnapBase
public import Dsverify.Proof.github_com.hashicorp.raft.FmtErrorf

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

open github_com.hashicorp.raft proto gprot

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem github_com.hashicorp.raft.Raft.takeSnapshot.wp_proof
    (wp_setLastSnapshot : github_com.hashicorp.raft.raftState.setLastSnapshot.spec (GF := GF) (hG := hG))
    (wp_compactLogs : github_com.hashicorp.raft.Raft.compactLogs.spec (GF := GF) (hG := hG))
    (wp_getSnapshotVersion : github_com.hashicorp.raft.getSnapshotVersion.spec (GF := GF) (hG := hG))
    (wp_Error : github_com.hashicorp.raft.deferError.Error.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.takeSnapshot.spec (GF := GF) (hG := hG) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

end proof

end Perennial
