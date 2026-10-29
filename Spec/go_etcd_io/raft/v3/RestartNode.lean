/- Lean-first (no Rocq counterpart).

## `RestartNode`

The node API's spec. (2026-10-28: moved here from `NodeApiDraft.lean`, where it was drafted over the
API's sealed predicates, now `InvNode.lean`'s; until then this file held the triple over raft's
internals, now the proof's private `RestartNode.specRaw`.)
-/
module

public import Proof.go_etcd_io.raft.v3.InvNode
public import Proof.go_etcd_io.raft.v3.InvNodeRule

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **`RestartNode(c)`**: starts node `cv.ID'` of a static cluster of voters `vs`
(`cluster_alloc_static`) from its boot token, on a fresh storage whose `InitialState` gives the
voters' conf state, and whose certificates are the cluster's (`storageCertLink`). Today's premises,
with the ghost ones (`rnInit`, `isCommitted γ []`, the term budget, `certLink`, the mode and
`snapIn`) replaced by `nodeRestartBoot` and `storageCertLink`. -/
abbrev RestartNode.spec : Prop :=
  ∀ (γ : Cluster) (N : Namespace) (vs : List w64) (c : Loc) (cv : Config) (lok si : GoInterfaceOk)
    (σ : StorState) (hs : HardStateM) (csm : ConfStateM),
  -- `NewRawNode`'s premises (unchanged)
  ConfigValid cv →
  cv.Logger' = interface.ok lok →
  cv.Storage' = interface.ok si →
  sint.Z cv.MaxInflightMsgs' < 2 ^ 62 →
  cv.DisableProposalForwarding' = false →
  cv.ReadOnlyOption' = W64 0 →
  cv.DisableConfChangeValidation' = false →
  (cv.MaxCommittedSizePerReady' ≠ W64 0 ∨ cv.MaxSizePerMsg' ≠ W64 0) →
  cv.AsyncStorageWrites' = false →
  cv.Applied' = W64 0 →
  -- an empty storage, the voters' conf state (unchanged)
  σ.prev = entryID.mk (W64 0) (W64 0) → σ.ents = [] → (uint.Z σ.ss.index' = 0 ∨ σ.ss = σ.prev) →
  σ.pend = [] → HsEmpty hs →
  csm.Voters' = vs → csm.VotersOutgoing' = [] → csm.Learners' = [] → csm.LearnersNext' = [] →
  csm.AutoLeave' = false →
  cv.ID' ∈ vs →
  σ.fl = W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗ isLogger lok ∗
      isStorageD (interface.ok si) ∗ ownStorage (interface.ok si) σ ∗
      □ (∀ (Φ : val → IProp GF) (ss' : entryID), ownStorage (interface.ok si) { σ with ss := ss' } -∗
           (∀ (hp cs : Loc) (al : Bool), ownStorage (interface.ok si) { σ with ss := ss' } -∗
            hsOpt hp hs -∗ csPts cs DFrac.discard csm al -∗
            Φ (PairV (PairV #hp #cs) #interface.nil)) -∗
           WP (App (Val #(methods si.ty go!"InitialState" si.v)) (Val #())) {{ Φ }}) ∗
      nodeRestartBoot γ N vs cv.ID' ∗ storageCertLink γ N (interface.ok si) }}
    (App (Val #(functions RestartNode [])) (Val #c))
  {{ (nd : GoInterface), RET #nd;
      ∃ (n : Loc), ⌜nd = interface.mkOk (go.GoType.PointerType node.ty) #n⌝ ∗
        isNode n γ N cv.ID' ∗ nodeDriver n γ N (NodeDriverState.init (interface.ok si)) }}

/-- **`RestartNode(c)` in a cluster with snapshots and reconfiguration** (2026-10-28, stage U4a;
`cluster_alloc_dec`, `InvNodeRule.lean`; until the conf-change decision switch `cluster_alloc_rule`): as `RestartNode.spec`, from a founder's token of the
cluster of the voters `vs` (`nodeFounder`) in place of `nodeRestartBoot`, **or** (2026-10-29, stage
U4) a newcomer's (`nodeJoin`, `joinAuth_join`), told that `vs` are the initial membership's voters
(`confAt` at `0`); the storage's `ConfState` the initial membership's either way, so a newcomer
starts at `c0` without being one of its voters (until U4 `cv.ID' ∈ vs`, which no founder needs
either); and the node's view of its configuration at the voters' membership, with nothing applied
(`nodeConfig`, as `StartNode.dynamicSpec`'s post). (A known exception to one spec per function, as
the dynamic variants, until stage U9 makes this cluster the only one.) Scope: a newcomer starts at
`c0`, not on an empty `ConfState` as etcd's joining member does (the frozen design's F5). -/
abbrev RestartNode.unifiedSpec : Prop :=
  ∀ (γ : Cluster) (N : Namespace) (vs : List w64) (c : Loc) (cv : Config) (lok si : GoInterfaceOk)
    (σ : StorState) (hs : HardStateM) (csm : ConfStateM),
  -- `NewRawNode`'s premises (as `RestartNode.spec`'s)
  ConfigValid cv →
  cv.Logger' = interface.ok lok →
  cv.Storage' = interface.ok si →
  sint.Z cv.MaxInflightMsgs' < 2 ^ 62 →
  cv.DisableProposalForwarding' = false →
  cv.ReadOnlyOption' = W64 0 →
  cv.DisableConfChangeValidation' = false →
  (cv.MaxCommittedSizePerReady' ≠ W64 0 ∨ cv.MaxSizePerMsg' ≠ W64 0) →
  cv.AsyncStorageWrites' = false →
  cv.Applied' = W64 0 →
  -- an empty storage, the voters' conf state
  σ.prev = entryID.mk (W64 0) (W64 0) → σ.ents = [] → (uint.Z σ.ss.index' = 0 ∨ σ.ss = σ.prev) →
  σ.pend = [] → HsEmpty hs →
  csm.Voters' = vs → csm.VotersOutgoing' = [] → csm.Learners' = [] → csm.LearnersNext' = [] →
  csm.AutoLeave' = false →
  σ.fl = W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗ isLogger lok ∗
      isStorageD (interface.ok si) ∗ ownStorage (interface.ok si) σ ∗
      □ (∀ (Φ : val → IProp GF) (ss' : entryID), ownStorage (interface.ok si) { σ with ss := ss' } -∗
           (∀ (hp cs : Loc) (al : Bool), ownStorage (interface.ok si) { σ with ss := ss' } -∗
            hsOpt hp hs -∗ csPts cs DFrac.discard csm al -∗
            Φ (PairV (PairV #hp #cs) #interface.nil)) -∗
           WP (App (Val #(methods si.ty go!"InitialState" si.v)) (Val #())) {{ Φ }}) ∗
      (nodeFounder γ N vs cv.ID' ∨
        (nodeJoin γ N cv.ID' ∗ confAt γ 0 (Membership.simple (GMap.listToSet vs)) ∗ ⌜vs.Nodup⌝)) ∗
      storageCertLink γ N (interface.ok si) }}
    (App (Val #(functions RestartNode [])) (Val #c))
  {{ (nd : GoInterface), RET #nd;
      ∃ (n : Loc), ⌜nd = interface.mkOk (go.GoType.PointerType node.ty) #n⌝ ∗
        isNode n γ N cv.ID' ∗ nodeDriver n γ N (NodeDriverState.init (interface.ok si)) ∗
        nodeConfig n γ N ⟨0, Membership.simple (GMap.listToSet vs)⟩∗
        -- (2026-10-29, stage U9a) the node runs (`node.Stop` takes it whole)
        nodeRunning n γ N 1 }}

end spec

end EtcdGrove
end Perennial
