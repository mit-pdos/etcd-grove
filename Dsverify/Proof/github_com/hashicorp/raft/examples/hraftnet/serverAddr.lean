/-
`hraftnet.serverAddr`'s proof: `strconv.Itoa(int(s))`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.serverAddr
public import Perennial.Proof.strconv.Link
@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft.examples.hraftnet

open github_com.hashicorp.raft

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

set_option goose.wp.extras true

theorem serverAddr.wp_proof : serverAddr.spec (GF := GF) := by
  intro s
  wp_start as -
  wp_auto
  wp_apply strconv.wp_Itoa
  unfold sidOf
  iapply HΦ
  itrivial

end proof

end github_com.hashicorp.raft.examples.hraftnet

end Perennial
