/- Lean-first (no Rocq counterpart).

## `StartNode`

The node API's spec (2026-10-30, stage R5; until U9, 2026-10-29, the static cluster's
`StartNode.spec` and the dynamic one's `StartNode.dynamicSpec`, deleted with them).
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

/-- **`StartNode(c, peers)` in a cluster with a bootstrap log** (2026-10-30, stage R5;
`cluster_alloc` with a non-empty `boot`, `InvNodeRule.lean`): starts node `cv.ID'` from its start
token (`nodeBoot`), of the cluster of the voters `vs`, the peers `peers` those voters with the
contexts `ctxs` (`peersCtx`). raft's `Bootstrap` appends the voters' `AddNode`s, the cluster's
bootstrap log, committed, which the first `Ready`s hand out for the application to apply
(`node.ApplyConfChange`; each a no-op at the voters' membership).

The storage is a fresh one to boot from (`bootStorage`, as `RestartNode.spec`'s), its `InitialState`
answering the empty hard state and the **empty** conf state: a new cluster's (`Bootstrap` installs
the voters; a bare `MemoryStorage`'s answer). The post is `RestartNode.spec`'s: the node, its `Ready`
loop's token, its view of the configuration at the voters' membership with nothing applied, its
running token and the frame `InitialState` gave back; and the peers' slice. -/
abbrev StartNode.spec : Prop :=
  ∀ (γ : Cluster) (N : Namespace) (vs : List w64) (ctxs : List (List w8)) (c : Loc) (cv : Config)
    (lok si : GoInterfaceOk) (hs : HardStateM) (csm : ConfStateM) (Q : IProp GF)
    (peers : GoSlice) (dq : DFrac) (pv : List Peer),
  -- `NewRawNode`'s premises
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
  -- the empty hard state, the empty conf state (a new cluster's)
  HsEmpty hs →
  csm.Voters' = [] → csm.VotersOutgoing' = [] → csm.Learners' = [] → csm.LearnersNext' = [] →
  csm.AutoLeave' = false →
  -- the peers are the cluster's voters
  vs = pv.map Peer.ID' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗ isLogger lok ∗
      bootStorage γ cv.ID' (interface.ok si) hs csm Q ∗
      peers ↦*{dq} pv ∗ peersCtx pv ctxs ∗ nodeBoot γ N vs ctxs cv.ID' }}
    (App (App (Val #(functions StartNode [])) (Val #c)) (Val #peers))
  {{ (nd : GoInterface), RET #nd;
      ∃ (n : Loc), ⌜nd = interface.mkOk (go.GoType.PointerType node.ty) #n⌝ ∗
        isNode n γ N cv.ID' ∗ nodeDriver n γ N (NodeDriverState.init (interface.ok si)) ∗
        nodeConfig n γ N ⟨0, Membership.simple (GMap.listToSet vs)⟩ ∗
        nodeRunning n γ N 1 ∗ Q ∗ peers ↦*{dq} pv }}

end spec

end EtcdGrove
end Perennial
