/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/EncodeConfiguration.lean (241f27e).
-/
/-
The proof of `raft.EncodeConfiguration`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.EncodeConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.encodeConfigurationBytes

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

theorem github_com.hashicorp.raft.EncodeConfiguration.wp_proof
    (wp_encodeConfigurationBytes :
      github_com.hashicorp.raft.encodeConfigurationBytes.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.EncodeConfiguration.spec (GF := GF) (hG := hG) := by
  intro c ss dq
  wp_start as Hs
  wp_auto
  wp_apply wp_encodeConfigurationBytes $$ [$Hs] as %b ⟨Hs, Hb⟩
  iapply HΦ
  iframe

end proof

end Perennial
