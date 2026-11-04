/-
`NewDaemonSetsController(ctx, dsInformer, historyInformer, podInformer, nodeInformer, kubeClient,
failedPodsBackoff)` (`daemon_controller.go:158`): the controller. Lean-first; track C of the
DaemonSet run (`notes/k8s-daemonset-run/design.md`, "The controller object").

**What the code does** (read 2026-11-03 at the pin): a broadcaster (`record.NewBroadcaster`), the
logger of `ctx`; the gate `StaleControllerConsistencyDaemonSet` read (on: the consistency store
over the pod and DaemonSet stores' `LastStoreSyncResourceVersion` getters, and the pod write
callback calling its `WroteAt`; off: the no-op store); the struct (two recorders, the pod and
revision controls over `kubeClient`, the expectations, the two rate-limiting queues); for each
informer: its handler registered (`AddEventHandlerWithOptions`, errors ignored), its lister and
`HasSynced` stored; the pod store's two indexers (`AddPodNodeNameIndexer`,
`AddPodControllerIndexer`, errors ignored), its indexer; the sync handler and the enqueuer (method
values), the backoff; `metrics.Register()`; returns the controller and `nil`.

**The spec.** From the factory's four typed informers (`typedInfAt`, track A) over the model
server's non-admin clientset (`clientIs`), a backoff (`isBackoff`), the gate on (`dsGateIs`), a
pod family with the two indexers' relations (`podFamOk`: the factory's caller chooses the family)
and a thread bound under the reader pools' size (B's `dscPools` are allocated from the
expectations' and consistency store's reader slots, `threadPool.init`), the error is `nil` and the
controller is `isDsc` (track B) with `dscRun`; and the caller gets the fresh state S1's
invariant takes (`dscFresh`: the consistency store's empty state, the owner tokens' authority),
which `Main` puts into `s1Inv` (B's design: allocated after the constructor). The four informers'
not-started parts (decision R6, `facNotStarted`: the callers' halves the factory's constructor
gave) go to the registrations, each pending until its contract is given (decision R7,
`handlerPending`), and to `AddIndexers` (given back). The handlers' contracts need the controller's
fields (stored after the registrations) and `s1Inv` (the delete handler's `Clear` fires inside it),
which `Main` allocates after the constructor: so the post's `dscActivate` gives the tokens back
whole once the caller has S1's invariants (the handlers activated, `handlerPending_activate`),
for `factory.Start`. **Scope** (decision R8): the model's ambiguous writes off
(`⌜cfg.AmbiguousWrites' = false⌝`, which `isDsc` carries): with them, a create that commits and
reports a timeout breaks S1 (`issues/k8s-daemonset-ambiguous-create-duplicate-pod.md`). The right to
register the controller's metric (`prometheus.nameFree dsMetricName`) goes to `metrics.Register`.
The registered handlers' resource is `True` (each call gets and returns its
listener's thread token, R7).

**Open (the run's report).** `isDsc`'s `podCtlIndexed` needs the index `podController` to be the
controller's relation: `AddPodControllerIndexer` adds it only if no index of that name exists
(review 1 (API), M1: the name-keyed index relations, track A's change in progress);
`isDsc`'s pools and the expectations' key function come from track B's changes in progress (the
informers' pools; the `ExpKeyFunc` package fact). In the proof, not the statement.
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.daemon.LifeDefs

@[expose] public section

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI apimodel informer informers cache workqueue k8s_io.kubernetes.pkg.controller.daemon

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.daemon.Assumptions]

/-- **`NewDaemonSetsController(...)`**: see the file header. -/
abbrev NewDaemonSetsController.spec : Prop :=
  ∀  (ctx : GoInterface) (lds lcr lpod lnode f : Loc) (γF : FacNames) (γa : ApiNames)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (Fams : Res → GoString → Fn GF) (kc : k8s_io.client_go.kubernetes.Interface) (bo : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller.daemon ∗ ⌜ctx ≠ interface.nil⌝ ∗
      isFactory f γF γa cfg Fams ∗ ⌜podFamOk (Fams .pods)⌝ ∗
      typedInfAt .daemonSets lds f ∗ typedInfAt .revisions lcr f ∗ typedInfAt .pods lpod f ∗
      typedInfAt .nodes lnode f ∗ clientIs kc γa cfg ∗ isBackoff bo ∗
      dsGateIs k8s_io.kubernetes.pkg.features.StaleControllerConsistencyDaemonSet true ∗
      ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ ∗ ([∗list] r ∈ resAll, facNotStarted γF r 1) ∗
      ⌜cfg.AmbiguousWrites' = false⌝ ∗ prometheus.nameFree dsMetricName }}
    (App (App (App (App (App (App (App
      (Val (@! k8s_io.kubernetes.pkg.controller.daemon.NewDaemonSetsController)) (Val #ctx))
      (Val #(typedInfVal .daemonSets lds))) (Val #(typedInfVal .revisions lcr)))
      (Val #(typedInfVal .pods lpod))) (Val #(typedInfVal .nodes lnode))) (Val #kc)) (Val #bo))
  {{ (dsc : Loc), RET (PairV #dsc #(interface.nil : GoInterface));
      ∃ c : DscComp, isDsc dsc c cfg γa (dscFams Fams) ∗ dscRun dsc c ∗ dscFresh c ∗
        dscActivate c γa γF }}

end spec

end dsctl
end EtcdGrove
end Perennial
