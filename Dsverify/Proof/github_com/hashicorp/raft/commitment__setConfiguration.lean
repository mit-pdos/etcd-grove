/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/commitment__setConfiguration.lean (241f27e).
-/
/-
The proof of `raft.commitment.setConfiguration` (stage 4 interface: a new spec, to be proved).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.commitment__setConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.commitment__recalculate

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

theorem github_com.hashicorp.raft.commitment.setConfiguration.wp_proof
    (wp_recalculate : github_com.hashicorp.raft.commitment.recalculate.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.commitment.setConfiguration.spec (GF := GF) (hG := hG) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

end proof

end Perennial
