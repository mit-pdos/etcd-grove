/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/BootstrapCluster.lean (241f27e).
-/
/-
The proof of `raft.BootstrapCluster`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.BootstrapCluster
public import Dsverify.Spec.github_com.hashicorp.raft.ValidateConfig
public import Dsverify.Spec.github_com.hashicorp.raft.checkConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.HasExistingState
public import Dsverify.Spec.github_com.hashicorp.raft.EncodeConfiguration
public import Dsverify.Proof.github_com.hashicorp.raft.EncodingLemmas

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

theorem github_com.hashicorp.raft.BootstrapCluster.wp_proof
    (wp_ValidateConfig : github_com.hashicorp.raft.ValidateConfig.spec (GF := GF) (hG := hG))
    (wp_checkConfiguration : github_com.hashicorp.raft.checkConfiguration.spec (GF := GF) (hG := hG))
    (wp_HasExistingState : github_com.hashicorp.raft.HasExistingState.spec (GF := GF) (hG := hG))
    (wp_EncodeConfiguration :
      github_com.hashicorp.raft.EncodeConfiguration.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.BootstrapCluster.spec (GF := GF) (hG := hG) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

end proof

end Perennial
