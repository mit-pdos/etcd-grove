/-
**The DaemonSet driver's vocabulary** (`examples/k8sdaemonset/dsmain`; track C of the autoverify
run, `notes/k8s-daemonset-run/design.md`). Lean-first.

* `dsCfg`: `serverConfig()`'s value (every failure flag, 20%).
* `gatesSet`: what `setFeatureGates()` leaves: the controller's gate
  `StaleControllerConsistencyDaemonSet` on (read through `utilfeature.DefaultFeatureGate`,
  `dsGateIs`), client-go's `AtomicFIFO` on and `WatchListClient` off (read through
  `features.FeatureGates()`, which `pkg/features`' init makes an adapter over the same gate,
  `features.gateIs`). (Gap C7: the gates' initialization is names only; see `setFeatureGates`'
  spec.)
* `newNodeOk d`, `newDsOk d`: what the driver's two objects are, as the proofs need them (the
  node's name; the DaemonSet's namespace and name, its selector and template labels, an unbound
  template): the facts track B's `sceneOk` asks of an admin-created DaemonSet are among them.
* `s1Reader γa` (persistent): read access to the API state (`apiReader`'s shape) that also gives
  S1 for every UID at the state read: what the checker needs. `s1Reader_of_inv`: from the two
  invariants (track B's `apiInv`, `s1Inv`; S1 is `s1Ok`'s first field).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain.Base
public import Proof.k8s_io.kubernetes.pkg.controller.daemon.LifeDefs
public import Proof.k8s_io.client_go.features.GateDefs

@[expose] public section

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsmain

open Iris Iris.BI Iris.ProofMode apimodel dsctl

section pure
variable [GooseExts]

/-- **`serverConfig()`**: every failure, ambiguous writes included, at 20%. -/
def dsCfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config :=
  ⟨true, true, true, true, true, true, W64 20⟩

/-- **The scenario's node** (`newNode()`): named `target-node`. -/
def newNodeOk (d : kd.core.Node) : Prop :=
  d.ObjectMeta'.Name' = go!"target-node"

/-- **The scenario's DaemonSet** (`newDaemonSet()`): `default/ds-1`, and what track B's `dsWf`
asks of a stored DaemonSet but for the fields the model defaults (`prepareDaemonSet`: the
revision history limit; no collision count). -/
def newDsOk (d : kd.apps.DaemonSet) : Prop :=
  d.ObjectMeta'.Namespace' = go!"default" ∧ d.ObjectMeta'.Name' = go!"ds-1" ∧
  cache.noSlash d.ObjectMeta'.Namespace' ∧ cache.noSlash d.ObjectMeta'.Name' ∧
  labels.selValid (selOf d) ∧ selCovers d ∧ d.Spec'.Template'.Spec'.NodeName' = go!"" ∧
  d.Spec'.Template'.ObjectMeta'.Finalizers' = []

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The gates `setFeatureGates()` sets** (persistent): see the file header. -/
def gatesSet : IProp GF :=
  iprop(dsGateIs k8s_io.kubernetes.pkg.features.StaleControllerConsistencyDaemonSet true ∗
    features.gateIs k8s_io.client_go.features.AtomicFIFO true ∗
    features.gateIs k8s_io.client_go.features.WatchListClient false)

instance gatesSet_persistent : Persistent (gatesSet (GF := GF)) := by
  unfold gatesSet; infer_instance

/-- **Read access with S1** (persistent): a read's atomic step at the current API state, which
has at most one pod of each DaemonSet UID per target node, given back unchanged. -/
def s1Reader (γa : ApiNames) : IProp GF :=
  iprop(□ |={⊤, ∅}=> ∃ σ, apiState γa σ ∗ ⌜∀ u, S1 keyName opIn σ u⌝ ∗
    (apiState γa σ ={∅, ⊤}=∗ True))

instance s1Reader_persistent (γa : ApiNames) : Persistent (s1Reader (GF := GF) γa) := by
  unfold s1Reader; infer_instance

end defs

section qitem
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [workqueue.QItem (GF := GF) GoString go.string]

/-- **Read access with S1 from the two invariants**: open `apiInv` (the API state and the
mirror's half) and `s1Inv` (the other half, `s1Ok`: S1), agree on the state. A law the checker's
glue needs; its proof is pending (the invariants' agreement, `ghostVar_agree`). -/
theorem s1Reader_of_inv (γa : ApiNames) (γ : S1Names) (c : DscComp) :
    apiInv γa γ ∗ s1Inv γ c ⊢ s1Reader (GF := GF) γa := by
  sorry

end qitem

end dsmain
end EtcdGrove
end Perennial
