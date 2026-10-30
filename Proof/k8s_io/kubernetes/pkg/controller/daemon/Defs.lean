/-
**The DaemonSet controller's predicates** (`pkg/controller/daemon/daemon_controller.go`'s
`DaemonSetsController`; phase 5 of `notes/k8s-daemonset-plan.md`). Lean-first.

* `InfLoc`: an informer's fixed locations and ghost names (its store, `cache` over a
  `threadSafeMap`, its FIFO's and its invariant's names); `infAt γa r I Fam`: the informer of the
  model API server's resource `r`, its store's indices `Fam`, the informer invariant
  (`informer.infInv`: the store is the log's table at its version, versions monotone);
* `DscComp`: the controller's fixed components (the values its constructor stores);
* `isDsc dsc c γ cfg`: the controller `dsc` (persistent): every field read-only for good, with
  its component's predicate. The write callback `OnWrite` is the constructor's
  `podWriteCallback` closure (`onWriteFnOk`: a `WroteAt` of the consistency store); the sync
  handler is the method value `dsc.syncDaemonSet`, the enqueuer `dsc.enqueue`.
* `dscReaders`: what one thread of the controller (a worker, an event handler) holds to read:
  one reader slot of each informer's store, of the expectations' store, and `n` of the
  consistency store's.

`isDsc` is what `NewDaemonSetsController`'s spec will give (not proved this round): until then
every spec that takes it rests on that unproved spec, a premise, not an axiom.
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.daemon.S1Inv
public import Proof.k8s_io.kubernetes.pkg.controller.PodControlDefs
public import Proof.k8s_io.kubernetes.pkg.controller.ExpDefs
public import Proof.k8s_io.client_go.listers.Defs
public import Proof.k8s_io.client_go.util.workqueue.DelayingDefs
public import Proof.k8s_io.client_go.tools.cache.CacheDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI apimodel informer consistency cache workqueue
open k8s_io.kubernetes.pkg.controller.daemon

section comps
variable [GooseExts]

/-- An informer's fixed locations and ghost names. -/
structure InfLoc where
  ca : Loc
  ts : Loc
  kf : GoFunc
  γf : FifoNames
  γt : TsNames
  γi : InfNames
  res : k8s_io.apimachinery.pkg.runtime.schema.GroupResource

/-- **The controller's fixed components**: its clientset, recorder, pod control, expectations,
consistency store, the four informers and their listers, the two work queues, the failed-pods
backoff. -/
structure DscComp where
  kc : k8s_io.client_go.kubernetes.Interface
  recorder : k8s_io.client_go.tools.record.EventRecorder
  pc : k8s_io.kubernetes.pkg.controller.RealPodControl
  exp : Loc
  γe : ExpNames
  cons : Loc
  dsI : InfLoc
  crI : InfLoc
  podI : InfLoc
  nodeI : InfLoc
  dsl : Loc
  crl : Loc
  podl : Loc
  nodel : Loc
  q : Loc
  γq : DNames
  nq : Loc
  γnq : DNames
  backoff : Loc

end comps

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
/- The work queues' items, the DaemonSets' keys (an instance for `GoString` is not built yet: a
premise of `isDsc`). -/
variable [QItem (GF := GF) GoString go.string]

/-- **The informer of resource `r`** (persistent): its store over the informer's registered
objects (`infObj`), with indices `Fam`, and the informer invariant. -/
def infAt (γa : ApiNames) (r : Res) (I : InfLoc) (Fam : Nat → Fn GF) : IProp GF :=
  iprop(isCache I.ca I.ts I.γt (infObj I.γi r) Fam I.kf ∗ infInv γa r I.γf I.γt I.γi)

instance infAt_persistent (γa : ApiNames) (r : Res) (I : InfLoc) (Fam : Nat → Fn GF) :
    Persistent (infAt γa r I Fam) := by
  unfold infAt; infer_instance

/-- **The consistency store's getters' contract** for the DaemonSet controller: the pods'
store's `LastStoreSyncResourceVersion` returns a version its informer has reached for good, well
formed or empty (the DaemonSets' store: any). -/
def getterContract (γ : S1Names) : GR → GoString → IProp GF :=
  fun gr rv => if gr = podGR then
    iprop(⌜rv = [] ∨ resourceversion.wellFormed rv = true⌝ ∗
      infRvLb γ.podInf (resourceversion.decVal rv))
  else iprop(True)

/-- **`podWriteCallback`** (the constructor's closure over its consistency store `c`): for a pod
`p` and a controller reference `cref` (`refAt`), a `WroteAt` of the pod's version for the owner
`(pod namespace, reference name)` and UID the reference's, logically atomic over the store's
abstract state; with a `nil` reference, nothing. The caller holds the owner's permission and a
reader slot. -/
def onWriteFnOk (f : GoFunc) (c : Loc) (γc : ConsNames) (T : Owner → Qp → IProp GF) : IProp GF :=
  iprop(⌜f ≠ func.nil⌝ ∗ □ ∀ (p : Loc) (dq : DFrac) (dp : kd.core.Pod) (cref : Loc)
      (r : kd.meta.OwnerReference) (q : Qp) (Q : IProp GF) (Φ : val → IProp GF),
    podAt p dq dp -∗ refAt cref r -∗
    T ⟨dp.ObjectMeta'.Namespace', r.Name'⟩ q -∗ consReader c γc -∗
    ▷ (|={⊤ \ ↑consN, ∅}=> ∃ M, consState γc M ∗
        (consState γc (wroteAtM M ⟨dp.ObjectMeta'.Namespace', r.Name'⟩ r.UID' podGR
            dp.ObjectMeta'.ResourceVersion') ={∅, ⊤ \ ↑consN}=∗ Q)) -∗
    ▷ (podAt p dq dp -∗ T ⟨dp.ObjectMeta'.Namespace', r.Name'⟩ q -∗ consReader c γc -∗ Q -∗
        Φ #()) -∗
    WP (App (App (Val #f) (Val #p)) (Val #cref)) {{ Φ }})

instance onWriteFnOk_persistent (f : GoFunc) (c : Loc) (γc : ConsNames)
    (T : Owner → Qp → IProp GF) : Persistent (onWriteFnOk f c γc T) := by
  unfold onWriteFnOk; infer_instance

/-- **The controller** `dsc` (persistent): see the file header. `podFam` are the pod store's
indices (the node name and the controller UID, `AddPodNodeNameIndexer`,
`AddPodControllerIndexer`). -/
def isDsc (dsc : Loc) (c : DscComp) (γ : S1Names)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (podFam : Nat → Fn GF) (dsFam crFam nodeFam : Nat → Fn GF) : IProp GF :=
  iprop(
    "#HkubeClient" ∷ dsc.[DaemonSetsController, go!"kubeClient"] ↦□ c.kc ∗
    "#Hkc" ∷ clientIs c.kc γ.api cfg ∗
    "#HeventRecorder" ∷ dsc.[DaemonSetsController, go!"eventRecorder"] ↦□ c.recorder ∗
    "#Hrec" ∷ recorderOk c.recorder ∗
    "#HpodControl" ∷ dsc.[DaemonSetsController, go!"podControl"] ↦□
      (interface.mkOk k8s_io.kubernetes.pkg.controller.RealPodControl.ty #c.pc :
        k8s_io.kubernetes.pkg.controller.PodControlInterface) ∗
    "%HpcKc" ∷ ⌜c.pc.KubeClient' = c.kc⌝ ∗
    "#HpcRec" ∷ recorderOk c.pc.Recorder' ∗
    "#HonWrite" ∷ onWriteFnOk c.pc.OnWrite' c.cons γ.cons (syncTok γ) ∗
    "#HburstReplicas" ∷ dsc.[DaemonSetsController, go!"burstReplicas"] ↦□ (W64 250) ∗
    "#HsyncHandler" ∷ dsc.[DaemonSetsController, go!"syncHandler"] ↦□
      (methods (go.GoType.PointerType DaemonSetsController.ty) go!"syncDaemonSet" #dsc : GoFunc) ∗
    "#HenqueueDaemonSet" ∷ dsc.[DaemonSetsController, go!"enqueueDaemonSet"] ↦□
      (methods (go.GoType.PointerType DaemonSetsController.ty) go!"enqueue" #dsc : GoFunc) ∗
    "#Hexpectations" ∷ dsc.[DaemonSetsController, go!"expectations"] ↦□
      (interface.mkOk (go.GoType.PointerType
        k8s_io.kubernetes.pkg.controller.ControllerExpectations.ty) #c.exp :
        k8s_io.kubernetes.pkg.controller.ControllerExpectationsInterface) ∗
    "#Hexp" ∷ isExp c.exp c.γe ∗
    "#HconsistencyStore" ∷ dsc.[DaemonSetsController, go!"consistencyStore"] ↦□
      (interface.mkOk (go.GoType.PointerType k8s_io.client_go.util.consistency.consistencyStore.ty)
        #c.cons : k8s_io.client_go.util.consistency.ConsistencyStore) ∗
    "#Hcons" ∷ (∃ S, isCons c.cons γ.cons (syncTok γ) S (getterContract γ)) ∗
    "#HdsI" ∷ infAt γ.api .daemonSets c.dsI dsFam ∗
    "#HcrI" ∷ infAt γ.api .revisions c.crI crFam ∗
    "#HpodI" ∷ infAt γ.api .pods c.podI podFam ∗
    "#HnodeI" ∷ infAt γ.api .nodes c.nodeI nodeFam ∗
    "%HpodInf" ∷ ⌜c.podI.γi = γ.podInf⌝ ∗
    "#HdsLister" ∷ dsc.[DaemonSetsController, go!"dsLister"] ↦□
      (interface.mkOk (go.GoType.PointerType k8s_io.client_go.listers.apps.v1.daemonSetLister.ty)
        #c.dsl : k8s_io.client_go.listers.apps.v1.DaemonSetLister) ∗
    "#Hdsl" ∷ c.dsl.[k8s_io.client_go.listers.apps.v1.daemonSetLister, go!"ResourceIndexer"] ↦□
      listers.riVal c.dsI.ca c.dsI.res [] ∗
    "#HhistoryLister" ∷ dsc.[DaemonSetsController, go!"historyLister"] ↦□
      (interface.mkOk
        (go.GoType.PointerType k8s_io.client_go.listers.apps.v1.controllerRevisionLister.ty)
        #c.crl : k8s_io.client_go.listers.apps.v1.ControllerRevisionLister) ∗
    "#Hcrl" ∷ c.crl.[k8s_io.client_go.listers.apps.v1.controllerRevisionLister,
      go!"ResourceIndexer"] ↦□ listers.riVal c.crI.ca c.crI.res [] ∗
    "#HpodLister" ∷ dsc.[DaemonSetsController, go!"podLister"] ↦□
      (interface.mkOk (go.GoType.PointerType k8s_io.client_go.listers.core.v1.podLister.ty)
        #c.podl : k8s_io.client_go.listers.core.v1.PodLister) ∗
    "#Hpodl" ∷ c.podl.[k8s_io.client_go.listers.core.v1.podLister, go!"ResourceIndexer"] ↦□
      listers.riVal c.podI.ca c.podI.res [] ∗
    "#HpodIndexer" ∷ dsc.[DaemonSetsController, go!"podIndexer"] ↦□
      (interface.mkOk (go.GoType.PointerType k8s_io.client_go.tools.cache.cache.ty) #c.podI.ca :
        k8s_io.client_go.tools.cache.Indexer) ∗
    "#HnodeLister" ∷ dsc.[DaemonSetsController, go!"nodeLister"] ↦□
      (interface.mkOk (go.GoType.PointerType k8s_io.client_go.listers.core.v1.nodeLister.ty)
        #c.nodel : k8s_io.client_go.listers.core.v1.NodeLister) ∗
    "#Hnodel" ∷ c.nodel.[k8s_io.client_go.listers.core.v1.nodeLister, go!"ResourceIndexer"] ↦□
      listers.riVal c.nodeI.ca c.nodeI.res [] ∗
    "#Hqueue" ∷ dsc.[DaemonSetsController, go!"queue"] ↦□
      (interface.mkOk (go.GoType.PointerType (k8s_io.client_go.util.workqueue.rateLimitingType.ty go.string)) #c.q :
        k8s_io.client_go.util.workqueue.TypedRateLimitingInterface GoString) ∗
    "#Hq" ∷ (∃ P, isRateLimitingQueue (K := GoString) c.q c.γq P) ∗
    "#HnodeUpdateQueue" ∷ dsc.[DaemonSetsController, go!"nodeUpdateQueue"] ↦□
      (interface.mkOk (go.GoType.PointerType (k8s_io.client_go.util.workqueue.rateLimitingType.ty go.string)) #c.nq :
        k8s_io.client_go.util.workqueue.TypedRateLimitingInterface GoString) ∗
    "#Hnq" ∷ (∃ P, isRateLimitingQueue (K := GoString) c.nq c.γnq P) ∗
    "#HfailedPodsBackoff" ∷ dsc.[DaemonSetsController, go!"failedPodsBackoff"] ↦□ c.backoff)

instance isDsc_persistent (dsc : Loc) (c : DscComp) (γ : S1Names)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (podFam dsFam crFam nodeFam : Nat → Fn GF) :
    Persistent (isDsc dsc c γ cfg podFam dsFam crFam nodeFam) := by
  unfold isDsc named; infer_instance

/-- **What one thread of the controller holds to read**: a reader slot of each informer's store
and of the expectations', and `n` of the consistency store's. -/
def dscReaders (c : DscComp) (γ : S1Names) (podFam dsFam crFam nodeFam : Nat → Fn GF) (n : Nat) :
    IProp GF :=
  iprop(tsReader c.dsI.ts c.dsI.γt (infObj c.dsI.γi .daemonSets) dsFam ∗
    tsReader c.crI.ts c.crI.γt (infObj c.crI.γi .revisions) crFam ∗
    tsReader c.podI.ts c.podI.γt (infObj c.podI.γi .pods) podFam ∗
    tsReader c.nodeI.ts c.nodeI.γt (infObj c.nodeI.γi .nodes) nodeFam ∗
    expReader c.γe ∗
    [∗list] _x ∈ List.replicate n (), consReader c.cons γ.cons)

end defs

end dsctl
end EtcdGrove
end Perennial
