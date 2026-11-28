/-
The proof of `service.Store.StoreConfiguration`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.Store__StoreConfiguration

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.service.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.service github_com.hashicorp.raft
  github_com.hashicorp.raft.proto github_com.hashicorp.raft.gprot

theorem github_com.hashicorp.raft.examples.hraftnet.service.Store.StoreConfiguration.wp_proof :
    github_com.hashicorp.raft.examples.hraftnet.service.Store.StoreConfiguration.spec (GF := GF) (hG := hG) := by
  intro s k c
  wp_start
  wp_auto
  iapply HΦ; itrivial

end proof

end Perennial
