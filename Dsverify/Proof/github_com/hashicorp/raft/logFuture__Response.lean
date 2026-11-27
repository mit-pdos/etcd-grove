/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/logFuture__Response.lean (241f27e).
-/
/-
The proof of `raft.(*logFuture).Response`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.logFuture__Response

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

open github_com.hashicorp.raft proto

theorem github_com.hashicorp.raft.logFuture.Response.wp_proof :
    github_com.hashicorp.raft.logFuture.Response.spec (GF := GF) (hG := hG) := by
  intro f r dq
  wp_start as Hr
  wp_auto
  iapply HΦ $$ Hr

end proof

end Perennial
