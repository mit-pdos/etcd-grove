/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/appendStats.lean (241f27e).
-/
/-
The proof of `appendStats` (replication subsystem).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.appendStats

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

theorem github_com.hashicorp.raft.appendStats.wp_proof :
    github_com.hashicorp.raft.appendStats.spec (GF := GF) (hG := hG) :=
  fun peer start logs skip => by
  wp_start
  wp_auto
  cases skip <;> (wp_auto; iapply HΦ; itrivial)

end proof

end Perennial
