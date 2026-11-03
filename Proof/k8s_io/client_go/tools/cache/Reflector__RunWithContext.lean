/-
Proof of `Spec/k8s_io/client_go/tools/cache/Reflector__RunWithContext.lean`: a `sorry` stub (Stage 3 of the DaemonSet autoverify run,
track A), its hypotheses the specs of the callees its Go body calls.
Missing callee specs (next round): `wait.DelayFunc.Until` (apimachinery), the watch error
handler's contract (`DefaultWatchErrorHandler`, in `reflFixed2`'s `watchErrorHandler`).
-/
module

public import Spec.k8s_io.client_go.tools.cache.Reflector__RunWithContext
public import Spec.github_com.go_logr.logr.Logger__Info
public import Spec.github_com.go_logr.logr.Logger__V_ptr
public import Spec.k8s_io.client_go.tools.cache.Reflector__ListAndWatchWithContext
public import Spec.k8s_io.klog.v2.FromContext

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI apimodel cache informer k8s_io.client_go.tools.cache

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]
variable [ctx_sem : _root_.Perennial.context.Assumptions]

theorem Reflector.RunWithContext.wp_proof
    (wp_ListAndWatchWithContext : cache.Reflector.ListAndWatchWithContext.spec (GF := GF) (hG := hG))
    (wp_FromContext : klog.FromContext.spec (GF := GF) (hG := hG))
    (wp_V : logr.Logger.V_ptr.spec (GF := GF) (hG := hG))
    (wp_Info : logr.Logger.Info.spec (GF := GF) (hG := hG)) :
    Reflector.RunWithContext.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end cache
end EtcdGrove
end Perennial
