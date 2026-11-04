/-
Proof of `Spec/k8s_io/kubernetes/pkg/controller/daemon/DaemonSetsController__Run.lean` over its callees' specs. Lean-first; Stage 3 of the autoverify run
(track C, `notes/k8s-daemonset-run/design.md`): a stub.

The plan: see the spec's header. Each worker goroutine runs `UntilWithContext` with `R :=
threadTok` over `runWorker`'s (`runNodeUpdateWorker`'s) spec; the GC goroutine `Until` over
`Backoff.GC`'s; `wg.Go` (Perennial's body) over `WaitGroup.Add`/`Done`, `Wait` at the end.

Still to add as hypotheses (callees without a spec yet): `WaitGroup.Add`/`Done`/`Wait` (Perennial, `sync`), `Clientset.CoreV1` and `coreV1.Events` (the model's, for the events sink).
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__Run
public import Spec.k8s_io.apimachinery.pkg.util.runtime.HandleCrashWithContext
public import Spec.k8s_io.klog.v2.FromContext
public import Spec.github_com.go_logr.logr.Logger__Info
public import Spec.k8s_io.client_go.tools.cache.WaitForNamedCacheSyncWithContext
public import Spec.k8s_io.apimachinery.pkg.util.wait.UntilWithContext
public import Spec.k8s_io.apimachinery.pkg.util.wait.Until
public import Spec.k8s_io.client_go.util.flowcontrol.Backoff__GC
public import Spec.k8s_io.client_go.util.workqueue.rateLimitingType__ShutDown
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__runWorker
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__runNodeUpdateWorker

@[expose] public section

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode apimodel informer informers cache workqueue k8s_io.kubernetes.pkg.controller.daemon

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.daemon.Assumptions]
variable [ctx_sem : _root_.Perennial.context.Assumptions]
variable [cache_sem : k8s_io.client_go.tools.cache.Assumptions]
variable [klog_sem : k8s_io.klog.v2.Assumptions]
variable [logr_sem : github_com.go_logr.logr.Assumptions]
variable [wq_sem : k8s_io.client_go.util.workqueue.Assumptions]

theorem DaemonSetsController.Run.wp_proof
    (wp_HandleCrashWithContext : utilruntime.HandleCrashWithContext.spec (GF := GF) (hG := hG))
    (wp_FromContext : klog.FromContext.spec (GF := GF) (hG := hG))
    (wp_Info : logr.Logger.Info.spec (GF := GF) (hG := hG))
    (wp_WaitSync : cache.WaitForNamedCacheSyncWithContext.spec (GF := GF) (hG := hG))
    (wp_UntilWithContext : wait.UntilWithContext.spec (GF := GF) (hG := hG))
    (wp_Until : wait.Until.spec (GF := GF) (hG := hG))
    (wp_GC : flowcontrol.Backoff.GC.spec (GF := GF) (hG := hG))
    (wp_ShutDown : workqueue.rateLimitingType.ShutDown.spec (GF := GF) (hG := hG))
    (wp_runWorker : DaemonSetsController.runWorker.spec (GF := GF) (hG := hG))
    (wp_runNodeUpdateWorker : DaemonSetsController.runNodeUpdateWorker.spec (GF := GF) (hG := hG)) :
    DaemonSetsController.Run.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end dsctl
end EtcdGrove
end Perennial
