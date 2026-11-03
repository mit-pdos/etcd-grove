/-
Proof of `Spec/k8s_io/client_go/tools/cache/sharedIndexInformer__AddEventHandlerWithOptions.lean`: a `sorry` stub (Stage 3 of the DaemonSet autoverify run,
track A), its hypotheses the specs of the callees its Go body calls.
Missing callee specs (next round): `ptr.Deref` (k8s.io/utils), `newProcessListener`,
`determineResyncPeriod`, `sharedIndexInformer.HasSyncedChecker`, the clock's `Now`.
-/
module

public import Spec.k8s_io.client_go.tools.cache.sharedIndexInformer__AddEventHandlerWithOptions
public import Spec.fmt.Errorf
public import Spec.k8s_io.apimachinery.pkg.util.wait.Group__Start
public import Spec.k8s_io.client_go.tools.cache.cache__List
public import Spec.k8s_io.client_go.tools.cache.processorListener__add
public import Spec.k8s_io.client_go.tools.cache.sharedProcessor__addListener
public import Spec.k8s_io.klog.v2.Background

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

theorem sharedIndexInformer.AddEventHandlerWithOptions.wp_proof
    (wp_Background : klog.Background.spec (GF := GF) (hG := hG))
    (wp_addListener : cache.sharedProcessor.addListener.spec (GF := GF) (hG := hG))
    (wp_List : cache.cache.List.spec (GF := GF) (hG := hG))
    (wp_add : cache.processorListener.add.spec (GF := GF) (hG := hG))
    (wp_Group_Start : wait.Group.Start.spec (GF := GF) (hG := hG))
    (wp_Errorf : fmt.Errorf.spec (GF := GF) (hG := hG)) :
    sharedIndexInformer.AddEventHandlerWithOptions.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end cache
end EtcdGrove
end Perennial
