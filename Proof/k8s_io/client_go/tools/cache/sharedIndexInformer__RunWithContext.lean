/-
Proof of `Spec/k8s_io/client_go/tools/cache/sharedIndexInformer__RunWithContext.lean`: a `sorry` stub (Stage 3 of the DaemonSet autoverify run,
track A), its hypotheses the specs of the callees its Go body calls.
Missing callee specs (next round): `utilruntime.HandleCrashWithContext`, `HasStarted`,
`newQueueFIFO` (and `NewRealFIFOWithOptions`, taking the preallocated FIFO names),
`NewShardedListWatch`, `New` (the controller), `context.WithCancelCause`/`WithoutCancel`,
`errors.New`, `wait.Group.StartWithChannel`/`StartWithContext`, `HasSyncedChecker`, the
mutation detector's `Run`.
-/
module

public import Spec.k8s_io.client_go.tools.cache.sharedIndexInformer__RunWithContext
public import Spec.k8s_io.apimachinery.pkg.util.wait.Group__Start
public import Spec.k8s_io.client_go.tools.cache.controller__RunWithContext
public import Spec.k8s_io.client_go.tools.cache.sharedProcessor__run
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

theorem sharedIndexInformer.RunWithContext.wp_proof
    (wp_FromContext : klog.FromContext.spec (GF := GF) (hG := hG))
    (wp_Group_Start : wait.Group.Start.spec (GF := GF) (hG := hG))
    (wp_processor_run : cache.sharedProcessor.run.spec (GF := GF) (hG := hG))
    (wp_controller_RunWithContext : cache.controller.RunWithContext.spec (GF := GF) (hG := hG)) :
    sharedIndexInformer.RunWithContext.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end cache
end EtcdGrove
end Perennial
