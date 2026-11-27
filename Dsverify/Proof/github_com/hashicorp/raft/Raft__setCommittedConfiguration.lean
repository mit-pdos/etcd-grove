/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__setCommittedConfiguration.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).setCommittedConfiguration`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setCommittedConfiguration

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

theorem github_com.hashicorp.raft.Raft.setCommittedConfiguration.wp_proof :
    github_com.hashicorp.raft.Raft.setCommittedConfiguration.spec (GF := GF) (hG := hG) := by
  intro r c0 l i0 li c ci
  wp_start as Hc
  wp_auto
  iapply HΦ
  iframe

end proof

end Perennial
