/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8sdaemonset/apimodel/eventClient__CreateWithEventNamespaceWithContext.lean`. Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.eventClient__CreateWithEventNamespaceWithContext

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

theorem eventClient.CreateWithEventNamespaceWithContext.wp_proof : eventClient.CreateWithEventNamespaceWithContext.spec (GF := GF) (hG := hG) := by
  intro _ c e ctx
  wp_start
  wp_auto
  iapply HΦ
  itrivial

end proof

end apimodel
end EtcdGrove
end Perennial
