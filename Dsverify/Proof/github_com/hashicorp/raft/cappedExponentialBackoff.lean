/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/cappedExponentialBackoff.lean (241f27e).
-/
/-
The proof of `raft.cappedExponentialBackoff`: a loop doubling `base`; nothing is claimed about the result.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.cappedExponentialBackoff
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

open github_com.hashicorp.raft

theorem github_com.hashicorp.raft.cappedExponentialBackoff.wp_proof
    (wp_min : github_com.hashicorp.raft.min.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.cappedExponentialBackoff.spec (GF := GF) (hG := hG) :=
  fun base round limit cap => by
  wp_start as -
  wp_auto
  wp_apply wp_min
  ihave HI : (∃ (b : time.Duration) (p : w64),
      "base" ∷ base_ptr ↦ b ∗ "power" ∷ power_ptr ↦ p : IProp GF) $$ [base power]
  · iexists _, _; iframe
  wp_for HI
  wp_if_destruct
  · wp_if_destruct
    · wp_for_post
      iapply HΦ $$ []
      itrivial
    · wp_for_post
      iframe
      iexists _, _; iframe
  · wp_if_destruct
    · iapply HΦ $$ []
      itrivial
    · iapply HΦ $$ []
      itrivial

end proof

end Perennial
