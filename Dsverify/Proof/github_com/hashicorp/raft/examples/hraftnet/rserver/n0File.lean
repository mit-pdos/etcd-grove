/-
`rserver.n0File`'s proof (hraft_robust).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rserver.n0File

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.rserver.Assumptions]

theorem github_com.hashicorp.raft.examples.hraftnet.rserver.n0File.wp_proof :
    github_com.hashicorp.raft.examples.hraftnet.rserver.n0File.spec (GF := GF) (hG := hG) := by
  intro dir
  wp_start as -
  wp_auto
  iapply HΦ
  itrivial

end proof

end Perennial
