/-
**The DaemonSet controller's lifecycle vocabulary** (track C of the autoverify run,
`notes/k8s-daemonset-run/design.md`): what `NewDaemonSetsController` takes and gives beside
track B's `isDsc`, what `Run` reads, and the handlers' arguments. Lean-first.

* `typedInfVal r l`: resource `r`'s typed informer (`appsinformers.DaemonSetInformer`, ...) as the
  interface value the constructor takes; `typedInfAt r l f` (track A) says it is the factory's.
* `podNodeFn`, `podCtlFn`: the relations of the two indexers the constructor adds to the pod
  informer (`controller.AddPodNodeNameIndexer`, `AddPodControllerIndexer`): a pod's node name
  (none if empty), its `PodControllerIndexKey`. `podFamOk FamN`: the pod store's name-keyed family gives them
  under their names (the factory's caller chooses the family, `NewSharedInformerFactory`).
* `dscFams Fams`: the controller's families (track B's `DscFams`) from the factory's.
* `dsGateIs f b`: `utilfeature.DefaultFeatureGate.Enabled(f)` answers `b` (the constructor reads
  `StaleControllerConsistencyDaemonSet`, which selects the real consistency store, the one
  `isDsc` describes).
* `bcastOk eb`: the event broadcaster (`tools/record`, names only: a trusted no-op, events do not
  affect safety, `notes/k8s-daemonset-plan.md` "The cut"): its methods return; `NewRecorder`'s
  recorder is a `recorderOk` one.
* `isBackoff b`: the failed-pods backoff as `Backoff.GC` uses it (its clock, `backoffOk`, and its
  lock over its entries).
* `dscRun dsc c`: the fields only `Run` reads (the broadcaster, the four `InformerSynced`
  functions, the backoff): with `isDsc`, what `NewDaemonSetsController` gives and `Run` takes.
* `delArg γi r x`: a delete handler's argument: a registered object of `r`, or a
  `DeletedFinalStateUnknown` tombstone of one (the handlers' `obj.(*T)` and
  `tombstone.Obj.(*T)` assertions are checked, but a typed `nil` would panic in
  `metav1.GetControllerOf`).

**The handler resource** (A's `handlerSpec γa r γi h H`, per listener): the controller's
handlers read the DaemonSet lister and the expectations, so each call needs reader slots, which a
thread borrows from the controller's pools with its thread token (`dscPools`). A handler runs on
its listener's goroutine, whose token the listener contract passes through each call (decision
R7: `{{ H evs ∗ threadTok ∗ Q }} … {{ H (evs ++ [e]) ∗ threadTok }}`): so `H evs := True`. Nothing
about past events is needed: the delete handler's `Clear` is made harmless by the event's own
facts (`evFacts`) and S1's invariant. The handlers are registered pending and activated by
`dscActivate` once S1's invariants exist (R7).

* `dsMetricName`: the controller's one metric (`metrics.Register`'s counter, `daemonset_controller`
  subsystem): the right to register it (`prometheus.nameFree`) is the constructor's premise, from
  program start (`goose_adequacy_start`, review 1 (API), M4).
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.daemon.SyncDefs
public import Proof.k8s_io.client_go.informers.Defs
public import Proof.k8s_io.client_go.tools.cache.InformerDefs
public import Proof.github_com.prometheus.client_golang.prometheus.Registry

@[expose] public section

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI apimodel informer informers cache consistency workqueue
open k8s_io.kubernetes.pkg.controller.daemon

section pure
variable [GooseExts]

/-- **The controller's metric's name** (`metrics.DaemonsetRequeueSkips`: subsystem
`daemonset_controller`, name `stale_sync_skips_total`). -/
def dsMetricName : GoString := go!"daemonset_controller_stale_sync_skips_total"

/-- `controller.PodNodeNameKeyIndex`. -/
def podNodeIndex : GoString := go!"spec.nodeName"

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Resource `r`'s typed informer at `l`** as the interface value the constructor takes. -/
def typedInfVal (r : Res) (l : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType (typedInfTy r)) #l

/-- **`AddPodNodeNameIndexer`'s relation**: a pod's node name, none if empty. -/
def podNodeFn : Fn GF :=
  fun x vs => iprop(∃ p : kd.core.Pod, □ apimodel.objAt x DFrac.discard (.pod p) ∗
    ⌜vs = if p.Spec'.NodeName' = [] then [] else [p.Spec'.NodeName']⌝)

/-- **`AddPodControllerIndexer`'s relation**: a pod's `PodControllerIndexKey` (track B's
`podCtlKey` of its controller reference, `ctlOf`). -/
def podCtlFn : Fn GF :=
  fun x vs => iprop(∃ p : kd.core.Pod, □ apimodel.objAt x DFrac.discard (.pod p) ∗
    ⌜vs = [podCtlKey p.ObjectMeta'.Namespace' (ctlOf p)]⌝)

/-- **The pod store's family has the controller's two indexers' relations** (pure). -/
def podFamOk (FamN : GoString → Fn GF) : Prop :=
  FamN podNodeIndex = podNodeFn ∧ FamN podCtlIndex = podCtlFn

/-- **The controller's index families from the factory's** (track B's `DscFams`, name-keyed). -/
def dscFams (Fams : Res → GoString → Fn GF) : DscFams GF :=
  ⟨Fams .pods, Fams .daemonSets, Fams .revisions, Fams .nodes⟩

/-- **`utilfeature.DefaultFeatureGate.Enabled(f)` answers `b`** (persistent): the variable holds a
gate, read-only for good, whose `Enabled(f)` returns `b`. -/
def dsGateIs (f : val) (b : Bool) : IProp GF :=
  iprop(∃ g : GoInterfaceOk,
    globalAddr k8s_io.apiserver.pkg.util.feature.DefaultFeatureGate ↦□ GoInterface.ok g ∗
    □ ∀ Φ : val → IProp GF, ▷ Φ #b -∗
      WP (App (Val #(methods g.ty go!"Enabled" g.v)) (Val f)) {{ Φ }})

instance dsGateIs_persistent (f : val) (b : Bool) : Persistent (dsGateIs (GF := GF) f b) := by
  unfold dsGateIs; infer_instance

/-- **The event broadcaster** (persistent; `tools/record`, names only: see the file header):
`NewRecorder(scheme, source)` returns a `recorderOk` recorder, `StartStructuredLogging(v)` and
`StartRecordingToSink(sink)` return a watch, `Shutdown()` returns. -/
def bcastOk (eb : k8s_io.client_go.tools.record.EventBroadcaster) : IProp GF :=
  iprop(∃ i : GoInterfaceOk, ⌜eb = GoInterface.ok i⌝ ∗
    □ (∀ (sch : Loc) (src : k8s_io.api.core.v1.EventSource) (Φ : val → IProp GF),
        ▷ (∀ r : GoInterface, recorderOk r -∗ Φ #r) -∗
        WP (App (App (Val #(methods i.ty go!"NewRecorder" i.v)) (Val #sch)) (Val #src)) {{ Φ }}) ∗
    □ (∀ (v : w32) (Φ : val → IProp GF), ▷ (∀ w : GoInterface, Φ #w) -∗
        WP (App (Val #(methods i.ty go!"StartStructuredLogging" i.v)) (Val #v)) {{ Φ }}) ∗
    □ (∀ (sink : GoInterface) (Φ : val → IProp GF), ▷ (∀ w : GoInterface, Φ #w) -∗
        WP (App (Val #(methods i.ty go!"StartRecordingToSink" i.v)) (Val #sink)) {{ Φ }}) ∗
    □ (∀ Φ : val → IProp GF, ▷ Φ #() -∗
        WP (App (Val #(methods i.ty go!"Shutdown" i.v)) (Val #())) {{ Φ }}))

instance bcastOk_persistent (eb : k8s_io.client_go.tools.record.EventBroadcaster) :
    Persistent (bcastOk (GF := GF) eb) := by
  unfold bcastOk; infer_instance

/-- **The backoff's entries** at fraction `q` (its lock's resource): the entries map, its entries'
cells. -/
def backoffEntries (m : GoMap) (q : Qp) : IProp GF :=
  iprop(∃ M : GMap GoString Loc, m ↦${DFrac.own q} M ∗
    [∗map] _k ↦ e ∈ M, ∃ v : k8s_io.client_go.util.flowcontrol.backoffEntry, e ↦{DFrac.own q} v)

/-- **The failed-pods backoff, for `GC`** (persistent): its clock (`backoffOk`), its entries map
(the field read-only for good), `HasExpiredFunc` unset (the default expiry), its lock over the
entries. -/
def isBackoff (b : Loc) : IProp GF :=
  iprop(backoffOk b ∗ ∃ m : GoMap,
    structFieldRef k8s_io.client_go.util.flowcontrol.Backoff go!"perItemBackoff" b ↦□ m ∗
    structFieldRef k8s_io.client_go.util.flowcontrol.Backoff go!"HasExpiredFunc" b ↦□
      (func.nil : GoFunc) ∗
    sync.isRWMutexGuard (structFieldRef k8s_io.client_go.util.flowcontrol.Backoff go!"RWMutex" b)
      (backoffEntries m))

instance isBackoff_persistent (b : Loc) : Persistent (isBackoff (GF := GF) b) := by
  unfold isBackoff; infer_instance

/-- **What only `Run` reads of the controller** (persistent): the event broadcaster, the four
stores' `InformerSynced` functions (each its informer's `HasSynced`), the backoff for `GC`. -/
def dscRun (dsc : Loc) (c : DscComp) : IProp GF :=
  iprop(∃ (eb : k8s_io.client_go.tools.record.EventBroadcaster) (fds fcr fpod fnode : GoFunc),
    dsc.[DaemonSetsController, go!"eventBroadcaster"] ↦□ eb ∗ bcastOk eb ∗
    dsc.[DaemonSetsController, go!"dsStoreSynced"] ↦□ fds ∗ syncedFn fds c.dsI.γi ∗
    dsc.[DaemonSetsController, go!"historyStoreSynced"] ↦□ fcr ∗ syncedFn fcr c.crI.γi ∗
    dsc.[DaemonSetsController, go!"podStoreSynced"] ↦□ fpod ∗ syncedFn fpod c.podI.γi ∗
    dsc.[DaemonSetsController, go!"nodeStoreSynced"] ↦□ fnode ∗ syncedFn fnode c.nodeI.γi ∗
    isBackoff c.backoff)

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 512 in
instance dscRun_persistent (dsc : Loc) (c : DscComp) : Persistent (dscRun (GF := GF) dsc c) := by
  unfold dscRun; infer_instance

/-- **The fresh state S1's invariant takes from the constructor** (B's `s1Res`): the consistency
store's empty abstract state and the owner tokens' authority, no owner yet. `Main` allocates
`s1Inv` with them (B's design, `notes/k8s-daemonset-run/design.md`). -/
def dscFresh (c : DscComp) : IProp GF :=
  iprop(consState c.γc ∅ ∗ ghostMapAuth c.tok 1 (∅ : GMap Owner Unit))

/-- **The constructor's pending handlers** (decision R7, track A's deferred handler contract): once
S1's invariants exist (for any names `γ` the caller allocates them under), the four handlers the
constructor registered are activated (`handlerPending_activate`: their contracts hold over
`dscEnv`) and the informers' not-started tokens come back whole, for the factory's `Start`. -/
def dscActivate (c : DscComp) (γa : ApiNames) (γF : FacNames) : IProp GF :=
  iprop(∀ γ : S1Names, apiInv γa γ -∗ s1Inv γ c ={⊤}=∗ [∗list] r ∈ resAll, facNotStarted γF r 1)

/-- **A delete handler's argument** (persistent): a registered object of `r`, or a tombstone of
one. -/
def delArg (γi : InfNames) (r : Res) (x : GoInterface) : IProp GF :=
  iprop(∃ y : GoInterface, ⌜x = y ∨ ∃ k, x = tombstone k y⌝ ∗ infObj γi r y)

instance delArg_persistent (γi : InfNames) (r : Res) (x : GoInterface) :
    Persistent (delArg (GF := GF) γi r x) := by
  unfold delArg; infer_instance

/-- **The DaemonSets a lister read** (persistent): the slice's DaemonSets, each read-only for good
and a version of a DaemonSet in a past API state's log (track B's `dsSeen`). -/
def dssSeen (γa : ApiNames) (sl : GoSlice) : IProp GF :=
  iprop(∃ ls : List Loc, sl ↦*{DFrac.discard} ls ∗
    [∗list] p ∈ ls, ∃ (o : Owner) (d : kd.apps.DaemonSet), □ dsAt p DFrac.discard d ∗ dsSeen γa o d)

instance dssSeen_persistent (γa : ApiNames) (sl : GoSlice) :
    Persistent (dssSeen (GF := GF) γa sl) := by
  unfold dssSeen; infer_instance

/-- **A DaemonSet a lister read for the owner `o`** (persistent): read-only for good, a version of
the owner's DaemonSet in a past API state's log. -/
def dsSeenAt (γa : ApiNames) (ds : Loc) (o : Owner) : IProp GF :=
  iprop(∃ d : kd.apps.DaemonSet, □ dsAt ds DFrac.discard d ∗ dsSeen γa o d)

instance dsSeenAt_persistent (γa : ApiNames) (ds : Loc) (o : Owner) :
    Persistent (dsSeenAt (GF := GF) γa ds o) := by
  unfold dsSeenAt; infer_instance

end defs

end dsctl
end EtcdGrove
end Perennial
