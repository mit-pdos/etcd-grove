/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__compactLogsWithTrailing.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).compactLogsWithTrailing` (stage 3).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__compactLogsWithTrailing
public import Dsverify.Proof.github_com.hashicorp.raft.InstallBase
public import Dsverify.Spec.github_com.hashicorp.raft.min

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

theorem github_com.hashicorp.raft.Raft.compactLogsWithTrailing.wp_proof
    (wp_min : github_com.hashicorp.raft.min.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.compactLogsWithTrailing.spec (GF := GF) (hG := hG) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

end proof

end Perennial
