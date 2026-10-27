/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8sdaemonset/apimodel/emptyNode.lean`. Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.emptyNode

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apimodel

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8sdaemonset

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : apimodel.Assumptions]

theorem emptyNode.wp_proof : emptyNode.spec (GF := GF) (hG := hG) := by
  intro _
  wp_start
  wp_apply wp_alloc as %l Hl
  iapply HΦ
  unfold zeroObj objAt nodeAt
  iexists l
  isplitr
  · ipureintro; rfl
  iexists _
  iframe Hl
  iapply (kd.core.Node.own_zero_of _ rfl)

end proof

end apimodel
end EtcdGrove
end Perennial
