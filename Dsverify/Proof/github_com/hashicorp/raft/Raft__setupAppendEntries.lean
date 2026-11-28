/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__setupAppendEntries.lean (241f27e).
-/
/-
The proof of `Raft__setupAppendEntries` (replication subsystem).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setupAppendEntries
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__getRPCHeader
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getCommitIndex
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setPreviousLog
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setNewLogs

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

theorem github_com.hashicorp.raft.Raft.setupAppendEntries.wp_proof
    (wp_getRPCHeader : github_com.hashicorp.raft.Raft.getRPCHeader.spec (GF := GF) (hG := hG))
    (wp_getCommitIndex : github_com.hashicorp.raft.raftState.getCommitIndex.spec (GF := GF) (hG := hG))
    (wp_setPreviousLog : github_com.hashicorp.raft.Raft.setPreviousLog.spec (GF := GF) (hG := hG))
    (wp_setNewLogs : github_com.hashicorp.raft.Raft.setNewLogs.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.setupAppendEntries.spec (GF := GF) (hG := hG) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

end proof

end Perennial
