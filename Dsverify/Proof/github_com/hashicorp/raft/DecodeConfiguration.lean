/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/DecodeConfiguration.lean (241f27e).
-/
/-
The proof of `raft.DecodeConfiguration`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.DecodeConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.decodeConfigurationBytes

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

theorem github_com.hashicorp.raft.DecodeConfiguration.wp_proof
    (wp_decodeConfigurationBytes :
      github_com.hashicorp.raft.decodeConfigurationBytes.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.DecodeConfiguration.spec (GF := GF) (hG := hG) := by
  intro b ss dq
  wp_start as Hb
  wp_auto
  wp_apply wp_decodeConfigurationBytes $$ [$Hb] as %c ⟨Hb, Hc⟩
  iapply HΦ
  iframe

end proof

end Perennial
