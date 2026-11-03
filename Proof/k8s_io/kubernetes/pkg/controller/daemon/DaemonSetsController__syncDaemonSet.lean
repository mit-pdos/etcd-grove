/-
Proof of `Spec/k8s_io/kubernetes/pkg/controller/daemon/DaemonSetsController__syncDaemonSet.lean`
over its callees' specs and gap D2's body hypothesis
(`DaemonSetsController__syncDaemonSet_body.lean`). Lean-first; Stage 3 of the autoverify run
(track B): a stub.

The proof's plan (a glue proof but for `EnsureReady`): split the key (`SplitMetaNamespaceKey`:
`ownerOf key`); `EnsureReady(owner)` with the sync token's `ownerTok` and a borrowed reader slot,
its atomic update fired inside `s1Inv` (`ensureReady_step`, at the bound `L'` the getter contract
gives: `readyRec` with `getterContract`'s `infRvLb`): on success the ready token; the DaemonSet
from the lister (a registered object of the DaemonSet informer, a logged version of the owner's:
`dsArg`); not found: `DeleteExpectations` and `Clear` (no permission; the record goes, which keeps
`s1Ok`: a missing DaemonSet has no bookkeeping, and the model never deletes one, so the lister's
`NotFound` is a cache that has not seen the create); the node list (distinct names: the store's
keys); `constructHistory` (the hash, `crOf`); `SatisfiedExpectations`; `updateDaemonSet` with the
ready token, then `updateDaemonSetStatus` with the owner's permission.

Callee hypotheses still to add (specs to write or boundary specs to propose): `errors.As`,
`metrics.DaemonsetRequeueSkips` (`CounterVec.WithLabelValues`, `Inc`), `apierrors.IsNotFound`,
`labels.Everything`, `reflect.DeepEqual` of the selector, the recorder's `Eventf` (in `isDsc`),
`KeyFunc` (the package variable `DeletionHandlingMetaNamespaceKeyFunc`), the clock's `Now`/`Sub`
(in `isDsc`'s `backoffOk`), `logr`'s `V`/`Info`/`Error`.
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__syncDaemonSet
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__syncDaemonSet_body
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__constructHistory
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__updateDaemonSet
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__updateDaemonSetStatus
public import Spec.k8s_io.kubernetes.pkg.controller.ControllerExpectations__DeleteExpectations
public import Spec.k8s_io.kubernetes.pkg.controller.ControllerExpectations__SatisfiedExpectations
public import Spec.k8s_io.client_go.util.consistency.consistencyStore__EnsureReady
public import Spec.k8s_io.client_go.util.consistency.consistencyStore__Clear
public import Spec.k8s_io.client_go.tools.cache.SplitMetaNamespaceKey
public import Spec.k8s_io.client_go.listers.apps.v1.daemonSetLister__DaemonSets
public import Spec.k8s_io.client_go.listers.apps.v1.daemonSetNamespaceLister__Get
public import Spec.k8s_io.client_go.listers.core.v1.nodeLister__List
public import Spec.k8s_io.klog.v2.FromContext
public import Spec.fmt.Errorf

@[expose] public section

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode apimodel consistency k8s_io.kubernetes.pkg.controller.daemon

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.daemon.Assumptions]

theorem DaemonSetsController.syncDaemonSet.wp_proof
    (h_body : DaemonSetsController.syncDaemonSet_body.spec (GF := GF) (hG := hG))
    (wp_Split : cache.SplitMetaNamespaceKey.spec (GF := GF) (hG := hG))
    (wp_EnsureReady : consistency.consistencyStore.EnsureReady.spec (GF := GF) (hG := hG))
    (wp_Clear : consistency.consistencyStore.Clear.spec (GF := GF) (hG := hG))
    (wp_DaemonSets : appslisters.daemonSetLister.DaemonSets.spec (GF := GF) (hG := hG))
    (wp_DsGet : appslisters.daemonSetNamespaceLister.Get.spec (GF := GF) (hG := hG))
    (wp_NodeList : corelisters.nodeLister.List.spec (GF := GF) (hG := hG))
    (wp_DeleteExpectations : ControllerExpectations.DeleteExpectations.spec (GF := GF) (hG := hG))
    (wp_SatisfiedExpectations :
      ControllerExpectations.SatisfiedExpectations.spec (GF := GF) (hG := hG))
    (wp_constructHistory : DaemonSetsController.constructHistory.spec (GF := GF) (hG := hG))
    (wp_updateDaemonSet : DaemonSetsController.updateDaemonSet.spec (GF := GF) (hG := hG))
    (wp_updateDaemonSetStatus :
      DaemonSetsController.updateDaemonSetStatus.spec (GF := GF) (hG := hG))
    (wp_FromContext : klog.FromContext.spec (GF := GF) (hG := hG))
    (wp_Errorf : fmt.Errorf.spec (GF := GF) (hG := hG)) :
    DaemonSetsController.syncDaemonSet.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end dsctl
end EtcdGrove
end Perennial
