/-
**The scenario's facts S1's invariant carries** (pure; Stage 3 of the autoverify run,
`notes/k8s-daemonset-run/design.md`, "S1's invariant"). Lean-first.

The model API server (`examples/k8sdaemonset/apimodel`) has no DaemonSet `Update` or `Delete` (its
DaemonSet client: `Create`, `Get`, `List`, `Watch`, `UpdateStatus`, whose mutation changes only the
status, `dsStatusMut`), no pod `Update` or `Patch`, no controller-revision `Patch`; only the admin
creates DaemonSets and nodes, only the controller creates pods and revisions. So every object of
the API state, at every version of its log, is one the controller's sync made from a DaemonSet
that is still stored, unchanged but for its status. `sceneOk σ` states it, for every DaemonSet
(not only `Main`'s), over the logs (the informers' caches hold past versions):

* **DaemonSets** (`dsFixed`, `dsWf`): never deleted; every logged version has the stored one's
  UID, spec, annotations and collision count (`dsSame`); each stored one is well formed for the
  controller: a namespace and name with no `/` (its key is canonical), a non-empty namespace, a
  valid selector that selects every label set extending the template's (`selCovers`: so the
  controller never releases what it made), an unbound template with no finalizers (`NodeName` empty:
  its pods are deleted at once, never terminating), a revision history limit. Distinct
  DaemonSets have distinct UIDs and distinct revision names (`crName`, so `snapshot` never meets
  another DaemonSet's revision: no hash collision, the collision count never changes, the hash and
  so every pod's hash label stays the DaemonSet's `dsHash`). `crName` mentions the uninterpreted
  `computeHashD`, so only a creator that knows the revision names differ can extend the scene
  (`dsCreate_step`'s premise): one with one DaemonSet per namespace, as `Main`. This excludes
  `snapshot`'s hash-collision path (`update.go:564-583`), a scope restriction.
* **Pods** (`podOf`): controlled by a stored DaemonSet (exactly its `NewControllerRef`), in its
  namespace, with the template's labels, its hash label, unbound, `Pending`, not being deleted:
  so `ClaimPods` neither adopts nor releases (the model has no pod `Patch`), no pod is terminating
  or failed (the manage loop's surge and backoff branches are never taken), every pod is updated
  (`IsPodUpdated`: the rolling update creates and deletes nothing).
* **Controller revisions** (`crOf`): controlled by a stored DaemonSet, in its namespace, named
  `crName`, labelled with the template's labels and the hash, holding the template's patch: so
  `ClaimControllerRevisions` neither adopts nor releases (no revision `Patch` in the model), a
  DaemonSet has at most one revision in any cache (no `dedupCurHistories` pod `Patch`), no history
  lacks the hash label (`constructHistory`'s label write into a possibly `nil` map not reached).

**The boundary functions.** `ComputeHash` (fnv over `spew`'s dump) and `getPatch` (`json.Marshal`
of the DaemonSet, the template's part) are deterministic functions of their inputs: `computeHashD`
and `getPatchD` are their models, uninterpreted (`opaque`: no axiom; the boundary specs of
`dump.ForHash`, `fnv`, `rand.SafeEncodeString` and `json.Marshal`/`Unmarshal` are what tie the Go
calls to them, proposals of the run's report).
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.daemon.S1Model
public import Proof.k8s_io.kubernetes.pkg.controller.Defs
public import Proof.k8s_io.kubernetes.pkg.controller.daemon.util.Defs
public import Proof.k8s_io.apimachinery.pkg.apis.meta.v1.SelDefs
public import Proof.k8s_io.client_go.tools.cache.Keys

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open apimodel consistency

section scene
variable [GooseExts]

/-! ## The boundary functions' models -/

/-- **`getPatch(ds)`**: the patch bytes, a function of the DaemonSet's template (uninterpreted:
`json.Marshal` of `{"spec": {"template": ..., "$patch": "replace"}}`). -/
opaque getPatchD : kd.core.PodTemplateSpec → List w8

/-! ## The DaemonSet's derived values -/

/-- The template's labels (`nil`: none). -/
def dsTmplLabels (d : kd.apps.DaemonSet) : GMap GoString GoString :=
  d.Spec'.Template'.ObjectMeta'.Labels'.getD ∅

/-- **The DaemonSet's hash** (`snapshot`'s `ComputeHash(&ds.Spec.Template, ds.Status.CollisionCount)`). -/
def dsHash (d : kd.apps.DaemonSet) : GoString :=
  (computeHashD d.Spec'.Template' d.Status'.CollisionCount').val

/-- **The DaemonSet's revision name** (`snapshot`'s `ds.Name + "-" + hash`). -/
def crName (d : kd.apps.DaemonSet) : GoString := d.ObjectMeta'.Name' ++ go!"-" ++ dsHash d

/-- **The DaemonSet's controller reference** (`metav1.NewControllerRef(ds, controllerKind)`). -/
def ctlRefOf (d : kd.apps.DaemonSet) : kd.meta.OwnerReference :=
  ⟨go!"apps/v1", go!"DaemonSet", d.ObjectMeta'.Name', d.ObjectMeta'.UID', some true, some true⟩

/-- **The selector's value** (`labels.SelV`, what `LabelSelectorAsSelector` interprets). -/
def selOf (d : kd.apps.DaemonSet) : Option labels.SelV :=
  d.Spec'.Selector'.map (fun s => ⟨s.MatchLabels'.getD ∅,
    s.MatchExpressions'.map (fun r => ⟨r.Key', r.Operator', r.Values'⟩)⟩)

/-- `M ⊆ L` for label maps. -/
def lblSub (M L : GMap GoString GoString) : Prop := ∀ k v, M !! k = some v → L !! k = some v

/-- **The selector selects every label set extending the template's.** -/
def selCovers (d : kd.apps.DaemonSet) : Prop :=
  ∀ L, lblSub (dsTmplLabels d) L → labels.selMatch (selOf d) L

/-- **The DaemonSet stored for owner `o`** (its key). -/
def dsAtOwner (σ : St) (o : Owner) : Option kd.apps.DaemonSet :=
  match σ.dss.objs !! o with
  | some (.ds d) => some d
  | _ => none

/-! ## The facts -/

/-- **Two versions of one DaemonSet**: the same UID, spec, annotations, collision count. -/
def dsSame (d d' : kd.apps.DaemonSet) : Prop :=
  d.ObjectMeta'.UID' = d'.ObjectMeta'.UID' ∧ d.Spec' = d'.Spec' ∧
  d.ObjectMeta'.Annotations' = d'.ObjectMeta'.Annotations' ∧
  d.Status'.CollisionCount' = d'.Status'.CollisionCount'

/-- **A stored DaemonSet is well formed for the controller** (see the file header). -/
structure dsWf (d : kd.apps.DaemonSet) : Prop where
  nsName : cache.noSlash d.ObjectMeta'.Namespace' ∧ cache.noSlash d.ObjectMeta'.Name'
  nsNe : d.ObjectMeta'.Namespace' ≠ go!""
  selValid : labels.selValid (selOf d)
  selCovers : selCovers d
  unbound : d.Spec'.Template'.Spec'.NodeName' = go!""
  noFin : d.Spec'.Template'.ObjectMeta'.Finalizers' = []
  histLimit : d.Spec'.RevisionHistoryLimit'.isSome

/-- **A pod the controller made for `d`** (see the file header). -/
structure podOf (d : kd.apps.DaemonSet) (p : kd.core.Pod) : Prop where
  ref : p.ObjectMeta'.OwnerReferences' = [ctlRefOf d]
  ns : p.ObjectMeta'.Namespace' = d.ObjectMeta'.Namespace'
  lbls : lblSub (dsTmplLabels d) (p.ObjectMeta'.Labels'.getD ∅)
  hash : (p.ObjectMeta'.Labels'.getD ∅) !! hashKey = some (dsHash d)
  unbound : p.Spec'.NodeName' = go!""
  pending : p.Status'.Phase' = go!"Pending"
  live : p.ObjectMeta'.DeletionTimestamp' = none
  noFin : p.ObjectMeta'.Finalizers' = []

/-- **A controller revision the controller made for `d`** (see the file header). -/
structure crOf (d : kd.apps.DaemonSet) (r : kd.apps.ControllerRevision) : Prop where
  ref : r.ObjectMeta'.OwnerReferences' = [ctlRefOf d]
  ns : r.ObjectMeta'.Namespace' = d.ObjectMeta'.Namespace'
  name : r.ObjectMeta'.Name' = crName d
  lbls : r.ObjectMeta'.Labels' = some (<[hashKey := dsHash d]> (dsTmplLabels d))
  data : r.Data'.Raw' = getPatchD d.Spec'.Template'

/-- **The scenario's facts** (see the file header). -/
structure sceneOk (σ : St) : Prop where
  dsFixed : ∀ c ∈ σ.dss.log, c.typ ≠ .deleted ∧ ∃ d d', c.obj = .ds d ∧
    σ.dss.objs !! c.obj.key = some (.ds d') ∧ dsSame d d'
  dsWf : ∀ (o : Owner) d, dsAtOwner σ o = some d → dsWf d
  uidInj : ∀ (o o' : Owner) d d', dsAtOwner σ o = some d → dsAtOwner σ o' = some d' →
    d.ObjectMeta'.UID' = d'.ObjectMeta'.UID' → o = o'
  crNameInj : ∀ (o o' : Owner) d d', dsAtOwner σ o = some d → dsAtOwner σ o' = some d' →
    d.ObjectMeta'.Namespace' = d'.ObjectMeta'.Namespace' → crName d = crName d' → o = o'
  pods : ∀ c ∈ σ.pods.log, ∃ (p : kd.core.Pod) (o : Owner) (d : kd.apps.DaemonSet), c.obj = .pod p ∧ dsAtOwner σ o = some d ∧ podOf d p
  crs : ∀ c ∈ σ.crs.log, ∃ (r : kd.apps.ControllerRevision) (o : Owner) (d : kd.apps.DaemonSet), c.obj = .cr r ∧ dsAtOwner σ o = some d ∧ crOf d r

/-- The empty server's scene. -/
theorem sceneOk_empty : sceneOk St.empty := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [St.empty, dsAtOwner]

end scene

end dsctl
end EtcdGrove
end Perennial
