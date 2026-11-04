/-
Proof of `Spec/k8s_io/kubernetes/pkg/controller/FilterPodsByOwner.lean` over its callees' specs. Lean-first; Stage 3 of the autoverify run
(`notes/k8s-daemonset-run/`, track B): a stub.

`PodControllerIndexKey` (a body) needs its spec (`podCtlKey`); the first `ByIndex` fired inside the informer invariant (the store is the log's table at its version, `readFacts`).
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.FilterPodsByOwner
public import Spec.fmt.Errorf
public import Spec.k8s_io.apimachinery.pkg.util.runtime.HandleError
public import Spec.k8s_io.client_go.tools.cache.cache__ByIndex

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode apimodel cache k8s_io.kubernetes.pkg.controller

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.Assumptions]
variable [api_sem : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Assumptions]

theorem FilterPodsByOwner.wp_proof
    (wp_ByIndex : cache.cache.ByIndex.spec (GF := GF) (hG := hG))
    (wp_Errorf : fmt.Errorf.spec (GF := GF) (hG := hG))
    (wp_HandleError : utilruntime.HandleError.spec (GF := GF) (hG := hG)) :
    FilterPodsByOwner.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end dsctl
end EtcdGrove
end Perennial
