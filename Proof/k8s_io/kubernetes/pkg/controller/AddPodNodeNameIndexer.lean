/-
Proof of `Spec/k8s_io/kubernetes/pkg/controller/AddPodNodeNameIndexer.lean` over its callees' specs. Lean-first; Stage 3 of the autoverify run
(track C, `notes/k8s-daemonset-run/design.md`): a stub.

The plan: `GetIndexer()` and `GetIndexers()` (the name looked up), then `AddIndexers` of a one-entry map (`isInformer`).
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.AddPodNodeNameIndexer
public import Spec.k8s_io.client_go.tools.cache.cache__GetIndexers

@[expose] public section

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode apimodel informer cache

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [ctl_sem : k8s_io.kubernetes.pkg.controller.Assumptions]
variable [cache_sem : k8s_io.client_go.tools.cache.Assumptions]
variable [ctx_sem : _root_.Perennial.context.Assumptions]

theorem AddPodNodeNameIndexer.wp_proof
    (wp_GetIndexers : cache.cache.GetIndexers.spec (GF := GF) (hG := hG)) :
    AddPodNodeNameIndexer.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end dsctl
end EtcdGrove
end Perennial
