/-
`hraftnet.apiTimeout`'s proof.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.apiTimeout

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft.examples.hraftnet

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

set_option goose.wp.extras true

theorem apiTimeout.wp_proof : apiTimeout.spec (GF := GF) := by
  wp_start as -
  wp_auto
  iapply HΦ
  itrivial

end proof

end github_com.hashicorp.raft.examples.hraftnet

end Perennial
