/-
**The sync path's vocabulary** (the DaemonSet controller's internal specs below `syncDaemonSet`).
Lean-first; Stage 3 of the autoverify run (`notes/k8s-daemonset-run/design.md`). The specs it
serves are the package's internal helpers: they may mirror the code (the spec skill's "Scope").

* `dscEnv`: what every sync helper takes, persistent: the package, the controller, the two
  invariants.
* `dsSeen γa o d`, `dsArg γa ds o d`: the DaemonSet the sync read from its lister: `d` is a
  version, in a past API state's log, of the DaemonSet at owner `o` (so, by `sceneOk`, the stored
  one but for its status), at `ds`, read-only for good.
* `readyTok γ c o L`: the sync token after the sync's `EnsureReady` (`ensureReady_step`): the
  owner ready, at bound `L`.
* `nodesAt`, `podsAt`, `crsAt`, `podMapAt`: lists of cache objects (read-only for good) and the
  manage loop's node-to-pods map.
* `podsView γa u L Mp`: the pod map shows, at a version at least `L` of a past API state's pods'
  log, every pod of `u`: a node with no entry had none (what lets the sync claim the node), and
  every pod in the map is a logged one (so `sceneOk` says it is live and `Pending`).
* `nodesFree γa u L ns`: the nodes `ns` have no entry in such a map.
* `maxRevD`: `maxRevision`'s value.
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.daemon.S1Inv
public import Spec.fmt.Errorf

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI apimodel informer consistency

section pure
variable [GooseExts]

/-- **`maxRevision(histories)`**: the largest revision, `0` for none (as `int64`s). -/
def maxRevD (rs : List kd.apps.ControllerRevision) : w64 :=
  rs.foldl (fun m r => if sint.Z m < sint.Z r.Revision' then r.Revision' else m) (W64 0)

/-- **The pods of the map** at node `n`. -/
def podsOn (Mp : GMap GoString (List kd.core.Pod)) (n : GoString) : List kd.core.Pod :=
  (Mp !! n).getD []

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [workqueue.QItem (GF := GF) GoString go.string]

/-- **The controller's environment** (persistent). -/
def dscEnv (dsc : Loc) (c : DscComp)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (γa : ApiNames) (F : DscFams GF) (γ : S1Names) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller.daemon ∗
    isDsc dsc c cfg γa F ∗ apiInv γa γ ∗ s1Inv γ c)

instance dscEnv_persistent (dsc : Loc) (c : DscComp)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (γa : ApiNames) (F : DscFams GF) (γ : S1Names) :
    Persistent (dscEnv dsc c cfg γa F γ) := by
  unfold dscEnv; infer_instance

/-- **A cached version of owner `o`'s DaemonSet** (persistent). -/
def dsSeen (γa : ApiNames) (o : Owner) (d : kd.apps.DaemonSet) : IProp GF :=
  iprop(∃ σp : St, pastSt γa σp ∗ ⌜∃ ch ∈ σp.dss.log, ch.obj = .ds d ∧ ch.obj.key = o⌝)

instance dsSeen_persistent (γa : ApiNames) (o : Owner) (d : kd.apps.DaemonSet) :
    Persistent (dsSeen (GF := GF) γa o d) := by
  unfold dsSeen; infer_instance

/-- **The DaemonSet the sync read** (persistent). -/
def dsArg (γa : ApiNames) (ds : Loc) (o : Owner) (d : kd.apps.DaemonSet) : IProp GF :=
  iprop(□ dsAt ds DFrac.discard d ∗ dsSeen γa o d)

instance dsArg_persistent (γa : ApiNames) (ds : Loc) (o : Owner) (d : kd.apps.DaemonSet) :
    Persistent (dsArg (GF := GF) γa ds o d) := by
  unfold dsArg; infer_instance

/-- **The ready token**: the sync token after the sync's `EnsureReady`, the owner ready at bound
`L`. -/
def readyTok (γ : S1Names) (c : DscComp) (o : Owner) (L : Nat) : IProp GF :=
  iprop(ownerTok c o 1 ∗ seenTok γ o (L, true))

/-- **A list of nodes** (cache objects, read-only for good). -/
def nodesAt (nl : GoSlice) (ns : List kd.core.Node) : IProp GF :=
  iprop(∃ ps : List Loc, nl ↦*{DFrac.discard} ps ∗ ⌜ps.length = ns.length⌝ ∗
    [∗list] i ↦ p ∈ ps, ∃ n, ⌜ns[i]? = some n⌝ ∗ □ nodeAt p DFrac.discard n)

/-- **A list of pods** (the slice at `dq`, the pods cache objects, read-only for good). -/
def podsAt (pl : GoSlice) (dq : DFrac) (ps : List kd.core.Pod) : IProp GF :=
  iprop(∃ ls : List Loc, pl ↦*{dq} ls ∗ ⌜ls.length = ps.length⌝ ∗
    [∗list] i ↦ p ∈ ls, ∃ d, ⌜ps[i]? = some d⌝ ∗ □ podAt p DFrac.discard d)

/-- **A list of controller revisions** (the slice at `dq`, the revisions read-only for good). -/
def crsAt (hl : GoSlice) (dq : DFrac) (rs : List kd.apps.ControllerRevision) : IProp GF :=
  iprop(∃ ls : List Loc, hl ↦*{dq} ls ∗ ⌜ls.length = rs.length⌝ ∗
    [∗list] i ↦ p ∈ ls, ∃ r, ⌜rs[i]? = some r⌝ ∗ □ crAt p DFrac.discard r)

/-- **The node-to-pods map** (`map[string][]*v1.Pod`, owned, its slices owned). -/
def podMapAt (m : GoMap) (Mp : GMap GoString (List kd.core.Pod)) : IProp GF :=
  iprop(∃ M : GMap GoString GoSlice, m ↦$ M ∗ ⌜∀ n, (M !! n).isSome = (Mp !! n).isSome⌝ ∗
    [∗map] n ↦ sl ∈ M, podsAt sl (DFrac.own 1) (podsOn Mp n))

/-- **The pod map's view** (persistent): see the file header. -/
def podsView (γa : ApiNames) (u : GoString) (L : Nat) (Mp : GMap GoString (List kd.core.Pod)) :
    IProp GF :=
  iprop(∃ (σp : St) (v : Nat), pastSt γa σp ∗ ⌜L ≤ v ∧
    (∀ n, Mp !! n = none → ∀ k p, informer.tableAt σp.pods.log v !! k = some p →
      ¬ dsPodOn keyName opIn u n p) ∧
    (∀ n p, p ∈ podsOn Mp n → ∃ ch ∈ σp.pods.log, ch.obj = .pod p)⌝)

instance podsView_persistent (γa : ApiNames) (u : GoString) (L : Nat)
    (Mp : GMap GoString (List kd.core.Pod)) : Persistent (podsView (GF := GF) γa u L Mp) := by
  unfold podsView; infer_instance

/-- **The nodes a sync may create pods on** (persistent): a pod map with that view shows none
on them. -/
def nodesFree (γa : ApiNames) (u : GoString) (L : Nat) (ns : List GoString) : IProp GF :=
  iprop(∃ Mp, podsView γa u L Mp ∗ ⌜∀ n ∈ ns, Mp !! n = none⌝)

instance nodesFree_persistent (γa : ApiNames) (u : GoString) (L : Nat) (ns : List GoString) :
    Persistent (nodesFree (GF := GF) γa u L ns) := by
  unfold nodesFree; infer_instance

/-- **The pods a sync read, as a list** (persistent): at a version at least `L` of a past API
state's pods' log, every pod of `u` is in the list, and every pod of the list is a logged one. -/
def podsListView (γa : ApiNames) (u : GoString) (L : Nat) (ps : List kd.core.Pod) : IProp GF :=
  iprop(∃ (σp : St) (v : Nat), pastSt γa σp ∗ ⌜L ≤ v ∧
    (∀ k p, informer.tableAt σp.pods.log v !! k = some (.pod p) → ctlBy u p → p ∈ ps) ∧
    (∀ p ∈ ps, ∃ ch ∈ σp.pods.log, ch.obj = .pod p)⌝)

instance podsListView_persistent (γa : ApiNames) (u : GoString) (L : Nat)
    (ps : List kd.core.Pod) : Persistent (podsListView (GF := GF) γa u L ps) := by
  unfold podsListView; infer_instance

/-- **The DaemonSet's controller revisions a sync read** (pure): at most one, and it is the one
the controller made for `d` (`crOf`). -/
def crsOfDs (d : kd.apps.DaemonSet) (rs : List kd.apps.ControllerRevision) : Prop :=
  rs.length ≤ 1 ∧ ∀ r ∈ rs, crOf d r

end defs

end dsctl
end EtcdGrove
end Perennial
