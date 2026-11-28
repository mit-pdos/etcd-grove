/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__installSnapshot.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).installSnapshot` (stage 3, snap's riskiest step): the pending install
through the sink's `Close` (`snapProof.install_commit`), the FSM goroutine's restore (`fsmRestoreP`),
`setLastApplied` (`snapProof.install_applied_au`), the keep/discard step and the compaction.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__installSnapshot
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getCurrentTerm
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getLastApplied
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__setLastApplied
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__setLastSnapshot
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getLastLog
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__setLastLog
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setState
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setCurrentTerm
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setLeader
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setLastContact
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setLatestConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setCommittedConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__compactLogs
public import Dsverify.Spec.github_com.hashicorp.raft.DecodeConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__processConfigurationLogEntry
public import Dsverify.Spec.github_com.hashicorp.raft.RPC__Respond
public import Dsverify.Spec.github_com.hashicorp.raft.getSnapshotVersion
public import Dsverify.Spec.github_com.hashicorp.raft.newCountingReader
public import Dsverify.Spec.github_com.hashicorp.raft.countingReader__Read
public import Dsverify.Spec.github_com.hashicorp.raft.startSnapshotRestoreMonitor
public import Dsverify.Spec.github_com.hashicorp.raft.snapshotRestoreMonitor__StopAndWait
public import Dsverify.Proof.github_com.hashicorp.raft.InstallBase
public import Dsverify.Proof.github_com.hashicorp.raft.SnapFut
public import Spec.io.Copy

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
theorem github_com.hashicorp.raft.Raft.installSnapshot.wp_proof
    (wp_getCurrentTerm : github_com.hashicorp.raft.raftState.getCurrentTerm.spec (GF := GF) (hG := hG))
    (wp_getLastApplied : github_com.hashicorp.raft.raftState.getLastApplied.spec (GF := GF) (hG := hG))
    (wp_setLastApplied : github_com.hashicorp.raft.raftState.setLastApplied.spec (GF := GF) (hG := hG))
    (wp_setLastSnapshot : github_com.hashicorp.raft.raftState.setLastSnapshot.spec (GF := GF) (hG := hG))
    (wp_getLastLog : github_com.hashicorp.raft.raftState.getLastLog.spec (GF := GF) (hG := hG))
    (wp_setLastLog : github_com.hashicorp.raft.raftState.setLastLog.spec (GF := GF) (hG := hG))
    (wp_setState : github_com.hashicorp.raft.Raft.setState.spec (GF := GF) (hG := hG))
    (wp_setCurrentTerm : github_com.hashicorp.raft.Raft.setCurrentTerm.spec (GF := GF) (hG := hG))
    (wp_setLeader : github_com.hashicorp.raft.Raft.setLeader.spec (GF := GF) (hG := hG))
    (wp_setLastContact : github_com.hashicorp.raft.Raft.setLastContact.spec (GF := GF) (hG := hG))
    (wp_setLatestConfiguration :
      github_com.hashicorp.raft.Raft.setLatestConfiguration.spec (GF := GF) (hG := hG))
    (wp_setCommittedConfiguration :
      github_com.hashicorp.raft.Raft.setCommittedConfiguration.spec (GF := GF) (hG := hG))
    (wp_compactLogs : github_com.hashicorp.raft.Raft.compactLogs.spec (GF := GF) (hG := hG))
    (wp_DecodeConfiguration : github_com.hashicorp.raft.DecodeConfiguration.spec (GF := GF) (hG := hG))
    (wp_processConfigurationLogEntry :
      github_com.hashicorp.raft.Raft.processConfigurationLogEntry.spec (GF := GF) (hG := hG))
    (wp_Respond : github_com.hashicorp.raft.RPC.Respond.spec (GF := GF) (hG := hG))
    (wp_getSnapshotVersion : github_com.hashicorp.raft.getSnapshotVersion.spec (GF := GF) (hG := hG))
    (wp_newCountingReader : github_com.hashicorp.raft.newCountingReader.spec (GF := GF) (hG := hG))
    (wp_cr_Read : github_com.hashicorp.raft.countingReader.Read.spec (GF := GF) (hG := hG))
    (wp_startMonitor :
      github_com.hashicorp.raft.startSnapshotRestoreMonitor.spec (GF := GF) (hG := hG))
    (wp_StopAndWait :
      github_com.hashicorp.raft.snapshotRestoreMonitor.StopAndWait.spec (GF := GF) (hG := hG))
    (wp_Error : github_com.hashicorp.raft.deferError.Error.spec (GF := GF) (hG := hG))
    (wp_Copy : io.Copy.spec (GF := GF) (hG := hG))
    (wp_Copy_Discard : io.Copy_Discard.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.installSnapshot.spec (GF := GF) (hG := hG) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

end proof

end Perennial
