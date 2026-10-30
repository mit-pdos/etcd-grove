/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8sdaemonset/apimodel/emptyRevision.lean`. Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.emptyRevision

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apimodel

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8sdaemonset

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : apimodel.Assumptions]

theorem emptyRevision.wp_proof : emptyRevision.spec (GF := GF) (hG := hG) := by
  intro _
  wp_start
  wp_apply wp_alloc as %r Hr
  wp_apply wp_alloc as %l Hl
  iapply HΦ
  unfold zeroObj objAt crAt
  iexists l
  isplitr
  · ipureintro; rfl
  iexists _
  iframe Hl
  iapply (kd.apps.ControllerRevision.own_zero_of _ rfl)

end proof

end apimodel
end EtcdGrove
end Perennial
