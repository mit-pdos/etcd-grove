/-
**The DaemonSet controller's predicates** (`pkg/controller/daemon/daemon_controller.go`'s
`DaemonSetsController`; phase 5 of `notes/k8s-daemonset-plan.md`). Lean-first. Stage 3 of the
autoverify run (`notes/k8s-daemonset-run/design.md`, "The controller object"): the shape every
method takes and `NewDaemonSetsController` gives (track C proves the constructor).

* `InfLoc`: an informer's fixed locations and ghost names (its store, `cache` over a
  `threadSafeMap`, its FIFO's and its invariant's names); `infAt γa r I Fam`: the informer of the
  model API server's resource `r`, its store's indices `Fam`, the informer invariant
  (`informer.infInv`: the store is the log's table at its version, versions monotone);
* `DscComp`: the controller's fixed components (the values its constructor stores), with the ghost
  names it allocates: the consistency store's (`γc`), the per-owner tokens' (`tok`: the
  consistency store's permission `T`, `ownerTok`), the reader pools' (`pools`);
* `ownerTok c o q`: the consistency store's permission for owner `o` at fraction `q` (exclusive at
  `1`, `ownerTok_excl`); the sync of `o` holds it whole (`S1Inv.lean`'s `syncTok`), its create
  goroutines a fraction each;
* `dscPools c Fams`: one thread pool (`threadPool.isThreadPool`) per reader slot a thread of the
  controller uses: each informer store's, the expectations' and the consistency store's. A
  thread borrows a slot with its `threadTok` for each read and gives it back (`notes/bounds-plan.md`:
  the controller owns its locks' slots; specs take only `threadTok`);
* `isDsc dsc c cfg γa Fams`: the controller `dsc` (persistent): every field read-only for good,
  with its component's predicate. The write callback `OnWrite` is the constructor's
  `podWriteCallback` closure (`onWriteFnOk`: a `WroteAt` of the consistency store); the sync
  handler is the method value `dsc.syncDaemonSet`, the enqueuer `dsc.enqueue`.

**The work queue's keys.** The queue's items are `string`s and its spec says nothing of which items
`Get` hands out; the sync of `key` acts for the owner `SplitMetaNamespaceKey(key)`, so the owner's
exclusivity (the consistency store's documented precondition) needs the key to be the owner's
canonical one (`keyCanon`: `"/b"` and `"b"` name one owner). The controller only adds keys
`KeyFunc` made (canonical) or keys `Get` handed out. `queueKeysCanon` states the fact the proofs
need; it is what an item predicate of the work queue would give (`Add` taking `⌜Pk k⌝`, `Get`
returning it), a change to `util/workqueue`'s specs proposed in the run's report, until which
`NewDaemonSetsController`'s proof cannot establish it.
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.PodControlDefs
public import Proof.k8s_io.kubernetes.pkg.controller.ExpDefs
public import Proof.k8s_io.client_go.listers.Defs
public import Proof.k8s_io.client_go.util.workqueue.DelayingDefs
public import Proof.k8s_io.client_go.tools.cache.CacheDefs
public import Proof.k8s_io.client_go.tools.cache.InformerInv
public import Proof.k8s_io.client_go.tools.cache.Keys
public import Proof.k8s_io.client_go.util.consistency.Defs
public import Proof.k8s_io.kubernetes.pkg.controller.daemon.S1Model
public import Perennial.Proof.ThreadPool

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

/-- The reader pools' ghost names (`dscPools`). -/
structure DscPools where
  ds : GName
  cr : GName
  pod : GName
  node : GName
  exp : GName
  cons : GName

/-- **The controller's fixed components**: its clientset, recorder, pod control, expectations,
consistency store (its ghost names `γc`), the per-owner tokens' ghost map `tok`, the four
informers and their listers, the two work queues, the failed-pods backoff, the reader pools. -/
structure DscComp where
  kc : k8s_io.client_go.kubernetes.Interface
  recorder : k8s_io.client_go.tools.record.EventRecorder
  pc : k8s_io.kubernetes.pkg.controller.RealPodControl
  exp : Loc
  γe : ExpNames
  cons : Loc
  γc : ConsNames
  tok : GName
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
  pools : DscPools

/-- **The informers' index families**: the pod store's (the node name and the controller UID,
`AddPodNodeNameIndexer`, `AddPodControllerIndexer`) and the other three stores'. -/
structure DscFams (GF : BundledGFunctors) where
  pod : Nat → Fn GF
  ds : Nat → Fn GF
  cr : Nat → Fn GF
  node : Nat → Fn GF

/-! ### The work queue's keys -/

/-- **A canonical key**: if `SplitMetaNamespaceKey` accepts it, joining its parts back
(`MetaNamespaceKeyFunc`'s `nameKey`) gives the key. So distinct canonical keys split to distinct
owners. (`"/b"` is not canonical: it splits to `("", "b")`, whose key is `"b"`.) -/
def keyCanon (k : GoString) : Prop :=
  ∀ ns n, splitKey k = some (ns, n) → nameKey ns n = k

/-- **The owner a key names** (`SplitMetaNamespaceKey`), if any. -/
def ownerOf (k : GoString) : Option Owner :=
  (splitKey k).map (fun p => (⟨p.1, p.2⟩ : Owner))

/-- **The owner's canonical key** (`MetaNamespaceKeyFunc` of an object of that namespace and
name). -/
def ownerKey (o : Owner) : GoString := nameKey o.Namespace' o.Name'

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

/-- **The consistency store's permission for owner `o`** at fraction `q` (its `T`): an element of
the ghost map `c.tok`. -/
def ownerTok (c : DscComp) (o : Owner) (q : Qp) : IProp GF :=
  ghostMapElem c.tok o (DFrac.own q) ()

/-- The owners' permissions exclude each other at `1` (the consistency store's `tokExcl`). -/
theorem ownerTok_excl (c : DscComp) : ⊢ tokExcl (GF := GF) (ownerTok c) := by
  unfold tokExcl ownerTok
  iintro !> %o %q H1 H2
  ihave %Hv := ghostMapElem_valid_2 (K := Owner) (V := Unit) o c.tok (DFrac.own 1) (DFrac.own q)
    () () $$ H1 H2
  exfalso
  exact absurd (DFrac.valid_own_op Hv.1) (by simp)

/-- **The consistency store's getters' contract** for the DaemonSet controller: the pods'
store's `LastStoreSyncResourceVersion` returns a version its informer has reached for good, well
formed or empty (the DaemonSets' store: any). -/
def getterContract (c : DscComp) : GR → GoString → IProp GF :=
  fun gr rv => if gr = podGR then
    iprop(⌜rv = [] ∨ resourceversion.wellFormed rv = true⌝ ∗
      infRvLb c.podI.γi (resourceversion.decVal rv))
  else iprop(True)

/-- **`podWriteCallback`** (the constructor's closure over its consistency store `cs`): for a pod
`p` and a controller reference `cref` (`refAt`), a `WroteAt` of the pod's version for the owner
`(pod namespace, reference name)` and UID the reference's, logically atomic over the store's
abstract state; with a `nil` reference, nothing. The caller holds the owner's permission and a
reader slot. -/
def onWriteFnOk (f : GoFunc) (cs : Loc) (γc : ConsNames) (T : Owner → Qp → IProp GF) : IProp GF :=
  iprop(⌜f ≠ func.nil⌝ ∗ □ ∀ (p : Loc) (dq : DFrac) (dp : kd.core.Pod) (cref : Loc)
      (r : kd.meta.OwnerReference) (q : Qp) (Q : IProp GF) (Φ : val → IProp GF),
    podAt p dq dp -∗ refAt cref r -∗
    T ⟨dp.ObjectMeta'.Namespace', r.Name'⟩ q -∗ consReader cs γc -∗
    ▷ (|={⊤ \ ↑consN, ∅}=> ∃ M, consState γc M ∗
        (consState γc (wroteAtM M ⟨dp.ObjectMeta'.Namespace', r.Name'⟩ r.UID' podGR
            dp.ObjectMeta'.ResourceVersion') ={∅, ⊤ \ ↑consN}=∗ Q)) -∗
    ▷ (podAt p dq dp -∗ T ⟨dp.ObjectMeta'.Namespace', r.Name'⟩ q -∗ consReader cs γc -∗ Q -∗
        Φ #()) -∗
    WP (App (App (Val #f) (Val #p)) (Val #cref)) {{ Φ }})

instance onWriteFnOk_persistent (f : GoFunc) (cs : Loc) (γc : ConsNames)
    (T : Owner → Qp → IProp GF) : Persistent (onWriteFnOk f cs γc T) := by
  unfold onWriteFnOk; infer_instance

/-- **The failed-pods backoff** (persistent): its `Clock` field, read-only for good (the
controller reads it without the backoff's lock), holds a clock (`Now` returns). The backoff's
own methods (`IsInBackOffSinceUpdate`, `Get`, `Next`) run only for a failed pod, which the
model never has (`S1Steps.lean`'s `sceneOk`): no predicate for them. -/
def backoffOk (b : Loc) : IProp GF :=
  iprop(∃ clk : k8s_io.utils.clock.Clock,
    structFieldRef k8s_io.client_go.util.flowcontrol.Backoff go!"Clock" b ↦□ clk ∗ isClock clk)

instance backoffOk_persistent (b : Loc) : Persistent (backoffOk (GF := GF) b) := by
  unfold backoffOk; infer_instance

/-- The reader pools' namespaces. -/
def dscPoolN : Namespace := nroot.@"dscReaderPool"

/-- **The controller's reader pools** (persistent): a thread borrows one slot of a store's lock
with its `threadTok` (`threadPool.borrow`) and gives it back after the read. -/
def dscPools (c : DscComp) (F : DscFams GF) : IProp GF :=
  iprop(threadPool.isThreadPool (dscPoolN.@"ds") c.pools.ds
      (tsReader c.dsI.ts c.dsI.γt (infObj c.dsI.γi .daemonSets) F.ds) ∗
    threadPool.isThreadPool (dscPoolN.@"cr") c.pools.cr
      (tsReader c.crI.ts c.crI.γt (infObj c.crI.γi .revisions) F.cr) ∗
    threadPool.isThreadPool (dscPoolN.@"pod") c.pools.pod
      (tsReader c.podI.ts c.podI.γt (infObj c.podI.γi .pods) F.pod) ∗
    threadPool.isThreadPool (dscPoolN.@"node") c.pools.node
      (tsReader c.nodeI.ts c.nodeI.γt (infObj c.nodeI.γi .nodes) F.node) ∗
    threadPool.isThreadPool (dscPoolN.@"exp") c.pools.exp (expReader c.γe) ∗
    threadPool.isThreadPool (dscPoolN.@"cons") c.pools.cons (consReader c.cons c.γc))

instance dscPools_persistent (c : DscComp) (F : DscFams GF) :
    Persistent (dscPools c F) := by
  unfold dscPools; infer_instance

/-- **The work queue hands out canonical keys only** (persistent; see the file header: the fact an
item predicate of the work queue would give). -/
def queueKeysCanon (γq : DNames) : IProp GF :=
  iprop(□ ∀ k : GoString, keyTok γq.tq k -∗ ⌜keyCanon k⌝)

instance queueKeysCanon_persistent (γq : DNames) :
    Persistent (queueKeysCanon (GF := GF) γq) := by
  unfold queueKeysCanon; infer_instance

/-- **The controller** `dsc` (persistent): see the file header. -/
def isDsc (dsc : Loc) (c : DscComp)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (γa : ApiNames) (F : DscFams GF) : IProp GF :=
  iprop(
    "#HkubeClient" ∷ dsc.[DaemonSetsController, go!"kubeClient"] ↦□ c.kc ∗
    "#Hkc" ∷ clientIs c.kc γa cfg ∗
    "#HeventRecorder" ∷ dsc.[DaemonSetsController, go!"eventRecorder"] ↦□ c.recorder ∗
    "#Hrec" ∷ recorderOk c.recorder ∗
    "#HpodControl" ∷ dsc.[DaemonSetsController, go!"podControl"] ↦□
      (interface.mkOk k8s_io.kubernetes.pkg.controller.RealPodControl.ty #c.pc :
        k8s_io.kubernetes.pkg.controller.PodControlInterface) ∗
    "%HpcKc" ∷ ⌜c.pc.KubeClient' = c.kc⌝ ∗
    "#HpcRec" ∷ recorderOk c.pc.Recorder' ∗
    "#HonWrite" ∷ onWriteFnOk c.pc.OnWrite' c.cons c.γc (ownerTok c) ∗
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
    "#Hcons" ∷ (∃ S, isCons c.cons c.γc (ownerTok c) S (getterContract c)) ∗
    "#HdsI" ∷ infAt γa .daemonSets c.dsI F.ds ∗
    "#HcrI" ∷ infAt γa .revisions c.crI F.cr ∗
    "#HpodI" ∷ infAt γa .pods c.podI F.pod ∗
    "#HnodeI" ∷ infAt γa .nodes c.nodeI F.node ∗
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
    "#HqCanon" ∷ queueKeysCanon c.γq ∗
    "#HnodeUpdateQueue" ∷ dsc.[DaemonSetsController, go!"nodeUpdateQueue"] ↦□
      (interface.mkOk (go.GoType.PointerType (k8s_io.client_go.util.workqueue.rateLimitingType.ty go.string)) #c.nq :
        k8s_io.client_go.util.workqueue.TypedRateLimitingInterface GoString) ∗
    "#Hnq" ∷ (∃ P, isRateLimitingQueue (K := GoString) c.nq c.γnq P) ∗
    "#HfailedPodsBackoff" ∷ dsc.[DaemonSetsController, go!"failedPodsBackoff"] ↦□ c.backoff ∗
    "#Hbackoff" ∷ backoffOk c.backoff ∗
    "#Hpools" ∷ dscPools c F)

instance isDsc_persistent (dsc : Loc) (c : DscComp)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (γa : ApiNames) (F : DscFams GF) :
    Persistent (isDsc dsc c cfg γa F) := by
  unfold isDsc named; infer_instance

end defs

end dsctl
end EtcdGrove
end Perennial
