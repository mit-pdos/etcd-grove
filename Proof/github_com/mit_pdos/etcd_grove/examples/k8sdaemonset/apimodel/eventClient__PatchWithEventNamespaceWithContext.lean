/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8sdaemonset/apimodel/eventClient__PatchWithEventNamespaceWithContext.lean`. Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.eventClient__PatchWithEventNamespaceWithContext

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

theorem eventClient.PatchWithEventNamespaceWithContext.wp_proof : eventClient.PatchWithEventNamespaceWithContext.spec (GF := GF) (hG := hG) := by
  intro _ c e ctx data
  wp_start
  wp_auto
  iapply HΦ
  itrivial

end proof

end apimodel
end EtcdGrove
end Perennial
