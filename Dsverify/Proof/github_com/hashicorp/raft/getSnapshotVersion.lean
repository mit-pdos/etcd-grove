/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/getSnapshotVersion.lean (241f27e).
-/
/-
The proof of `raft.getSnapshotVersion` (stage 3, snap).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.getSnapshotVersion

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

theorem github_com.hashicorp.raft.getSnapshotVersion.wp_proof :
    github_com.hashicorp.raft.getSnapshotVersion.spec (GF := GF) (hG := hG) := by
  intro v
  wp_start
  wp_auto
  iapply HΦ; itrivial

end proof

end Perennial
