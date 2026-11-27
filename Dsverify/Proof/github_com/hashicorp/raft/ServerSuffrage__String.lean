/-
The proof of `raft.ServerSuffrage.String`. Lean-first.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.ServerSuffrage__String

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
theorem github_com.hashicorp.raft.ServerSuffrage.String.wp_proof :
    github_com.hashicorp.raft.ServerSuffrage.String.spec (GF := GF) (hG := hG) := by
  intro s
  wp_start as -
  wp_auto
  repeat' first | (iapply HΦ; itrivial) | wp_if_destruct

end proof

end Perennial
