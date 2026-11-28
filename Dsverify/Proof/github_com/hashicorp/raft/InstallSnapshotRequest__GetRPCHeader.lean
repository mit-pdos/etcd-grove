/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/InstallSnapshotRequest__GetRPCHeader.lean (241f27e).
-/
/-
The proof of `raft.(*InstallSnapshotRequest).GetRPCHeader`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.InstallSnapshotRequest__GetRPCHeader

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

open github_com.hashicorp.raft

theorem github_com.hashicorp.raft.InstallSnapshotRequest.GetRPCHeader.wp_proof :
    github_com.hashicorp.raft.InstallSnapshotRequest.GetRPCHeader.spec (GF := GF) (hG := hG) :=
  fun p rq => by
  wp_start as Hp
  wp_auto
  wp_end
