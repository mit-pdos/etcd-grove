/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/DefaultConfig.lean (241f27e).
-/
/-
The proof of `raft.DefaultConfig`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.DefaultConfig

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

theorem github_com.hashicorp.raft.DefaultConfig.wp_proof :
    github_com.hashicorp.raft.DefaultConfig.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  iapply HΦ
  unfold defaultConfig
  have h1 : (W64 1000 * W64 1000000 : w64) = W64 1000000000 := by decide
  have h2 : (W64 50 * W64 1000000 : w64) = W64 50000000 := by decide
  have h3 : (W64 120 * W64 1000000000 : w64) = W64 120000000000 := by decide
  have h4 : (W64 500 * W64 1000000 : w64) = W64 500000000 := by decide
  rw [h1, h2, h3, h4, show (chan.nil : GoChan) = null from rfl]
  iexact «$r0»

end proof

end Perennial
