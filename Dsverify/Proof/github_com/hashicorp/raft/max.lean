/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/max.lean (241f27e).
-/
/-
The proof of `raft.max`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.max

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

theorem github_com.hashicorp.raft.max.wp_proof :
    github_com.hashicorp.raft.max.spec (GF := GF) (hG := hG) :=
  fun a b => by
  wp_start as H
  wp_auto
  wp_if_destruct
  · simp only [if_pos (show uint.Z a ≥ uint.Z b by word)]
    wp_end
  · simp only [if_neg (show ¬ uint.Z a ≥ uint.Z b by word)]
    wp_end

end proof

end Perennial

