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
`cluster_alloc` with a non-empty `boot`, `InvNodeRule.lean`): starts node `cv.ID'`, one of the
voters `vs` of the cluster (`nodeBoot`, persistent since 2026-11-01), its id vacant (`nodeVacant`),
the peers `peers` those voters with the contexts `ctxs` (`peersCtx`). raft's `Bootstrap` appends
the voters' `AddNode`s, the cluster's bootstrap log, committed, which the first `Ready`s hand out for
the application to apply (`node.ApplyConfChange`; each a no-op at the voters' membership), and its
first `Ready` writes.

(2026-11-01, durability stage I-7) The client's update (`AU`) fires inside `StartNode` over its
durable state, which must be `RaftState.init` (a node that has stored nothing), and leaves it. The
storage is a fresh one (`restartStorage` at the empty contents: no snapshot, the hard state empty,
the base `⟨0, 0⟩`), its `InitialState` answering the **empty** conf state: a new cluster's
(`Bootstrap` installs the voters; a bare `MemoryStorage`'s answer). The post is `RestartNode.spec`'s:
the node, its `Ready` loop's token from the empty log (`NodeDriverState.init` at the storage's key),
its view of the configuration at the voters' membership with nothing applied, its running token,
the update's `COMM` and the storage's frame; and the peers' slice. -/
abbrev StartNode.spec : Prop :=
  ∀ (γ : Cluster) (N : Namespace) (vs : List w64) (ctxs : List (List w8)) (c : Loc) (cv : Config)
    (lok si : GoInterfaceOk) (csm : ConfStateM) (Q : IProp GF) (F : IProp GF)
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
  -- the empty conf state (a new cluster's)
  csm.Voters' = [] → csm.VotersOutgoing' = [] → csm.Learners' = [] → csm.LearnersNext' = [] →
  csm.AutoLeave' = false →
  -- the peers are the cluster's voters
  vs = pv.map Peer.ID' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗ isLogger lok ∗
      nodeBoot γ N vs ctxs cv.ID' ∗ nodeVacant γ cv.ID' ∗
      AU <{ ∃∃ (S : RaftState), raftState γ cv.ID' S ∗ ⌜S = RaftState.init⌝ }> @ ⊤ \ ↑N, ∅
         <{ raftState γ cv.ID' S, COMM Q }> ∗
      restartStorage γ (interface.ok si) ⟨hsZero, none, entryID.mk (W64 0) (W64 0), []⟩ csm 0 F ∗
      peers ↦*{dq} pv ∗ peersCtx pv ctxs }}
    (App (App (Val #(functions StartNode [])) (Val #c)) (Val #peers))
  {{ (nd : GoInterface), RET #nd;
      ∃ (n : Loc) (K : GName), ⌜nd = interface.mkOk (go.GoType.PointerType node.ty) #n⌝ ∗
        isNode n γ N cv.ID' ∗ nodeDriver n γ N (NodeDriverState.init (interface.ok si) K) ∗
        nodeConfig n γ N ⟨0, Membership.simple (GMap.listToSet vs)⟩ ∗
        nodeRunning n γ N 1 ∗ Q ∗ F ∗ peers ↦*{dq} pv }}

end spec

end EtcdGrove
end Perennial
