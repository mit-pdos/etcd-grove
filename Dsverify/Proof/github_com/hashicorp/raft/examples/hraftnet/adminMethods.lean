/-
`hraftnet.adminMethods`'s proof: a slice literal.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.adminMethods
@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.hashicorp.raft.examples.hraftnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote
open github_com.hashicorp.raft github_com.hashicorp.raft.gprot rpctransport service

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [π : NetProtoGS] [rsem : github_com.hashicorp.raft.Assumptions]

set_option goose.wp.extras true

theorem adminMethods.wp_proof : adminMethods.spec (GF := GF) := by
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
