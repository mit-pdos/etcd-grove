/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__heartbeat.lean (241f27e).
-/
/-
The proof of `Raft__heartbeat` (replication subsystem).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__heartbeat
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__getRPCHeader
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__config
public import Dsverify.Spec.github_com.hashicorp.raft.randomTimeout
public import Dsverify.Spec.github_com.hashicorp.raft.cappedExponentialBackoff
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__observe
public import Dsverify.Spec.github_com.hashicorp.raft.followerReplication__LastContact
public import Dsverify.Spec.github_com.hashicorp.raft.followerReplication__setLastContact
public import Dsverify.Spec.github_com.hashicorp.raft.verifyFuture__vote
public import Dsverify.Proof.github_com.hashicorp.raft.ReplNotify
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

theorem github_com.hashicorp.raft.Raft.heartbeat.wp_proof
    (wp_After : time.After.spec (GF := GF) (hG := hG))
    (wp_getRPCHeader : github_com.hashicorp.raft.Raft.getRPCHeader.spec (GF := GF) (hG := hG))
    (wp_config : github_com.hashicorp.raft.Raft.config.spec (GF := GF) (hG := hG))
    (wp_randomTimeout : github_com.hashicorp.raft.randomTimeout.spec (GF := GF) (hG := hG))
    (wp_cappedExponentialBackoff : github_com.hashicorp.raft.cappedExponentialBackoff.spec (GF := GF) (hG := hG))
    (wp_observe : github_com.hashicorp.raft.Raft.observe.spec (GF := GF) (hG := hG))
    (wp_LastContact : github_com.hashicorp.raft.followerReplication.LastContact.spec (GF := GF) (hG := hG))
    (wp_setLastContact : github_com.hashicorp.raft.followerReplication.setLastContact.spec (GF := GF) (hG := hG))
    (wp_vote : github_com.hashicorp.raft.verifyFuture.vote.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.heartbeat.spec (GF := GF) (hG := hG) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

end proof

end Perennial
