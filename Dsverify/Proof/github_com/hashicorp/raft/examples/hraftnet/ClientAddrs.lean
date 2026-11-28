/-
`hraftnet.ClientAddrs`'s proof: a slice literal.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.ClientAddrs

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

theorem ClientAddrs.wp_proof : ClientAddrs.spec (GF := GF) := by
  wp_start
  wp_auto
  wp_apply wp_slice_literal (V := GoString) (t := go.string) _
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  iapply HΦ
  iexists _
  iframe Hsl
  ipureintro; rfl

end proof

end github_com.hashicorp.raft.examples.hraftnet

end Perennial
