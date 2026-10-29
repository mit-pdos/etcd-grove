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

/-- **`RestartNode(c)` in a cluster with snapshots and reconfiguration** (2026-10-28, stage U4a;
`cluster_alloc`, `InvNodeRule.lean`): starts node `cv.ID'` from a founder's token of the
cluster of the voters `vs` (`nodeFounder`) **or** (2026-10-29, stage U4) a newcomer's (`nodeJoin`,
`joinAuth_join`), told that `vs` are the initial membership's voters (`confAt` at `0`); the
storage's `ConfState` the initial membership's either way; and the node's view of its
configuration at the voters' membership, with nothing applied (`nodeConfig`).

(U8 v2, 2026-10-29) The storage is a fresh one to boot from (`bootStorage`, the frozen design's
§3: its contract `isStorage γ cv.ID' st`, index `0` a frozen entry of term `0`, the last index `0`,
`InitialState` answering the empty hard state and the voters' conf state), the contract made by the
client once `InitialState` returned (`newRaft` reads `FirstIndex`/`LastIndex` first; a
`MemoryStorage`'s bundle is `memStorage_bootStorage`). (Until U8 v2 the storage's state `σ`,
`ownStorage`, its `InitialState` closure and `storageCertLink`; until then also the static
cluster's `RestartNode.spec`, dropped in U8 v2 ahead of U9.) Scope: a newcomer starts at `c0`, not
on an empty `ConfState` as etcd's joining member does (the frozen design's F5). -/
abbrev RestartNode.spec : Prop :=
  ∀ (γ : Cluster) (N : Namespace) (vs : List w64) (c : Loc) (cv : Config) (lok si : GoInterfaceOk)
    (hs : HardStateM) (csm : ConfStateM),
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
  -- the empty hard state, the voters' conf state
  HsEmpty hs →
  csm.Voters' = vs → csm.VotersOutgoing' = [] → csm.Learners' = [] → csm.LearnersNext' = [] →
  csm.AutoLeave' = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗ isLogger lok ∗
      bootStorage γ cv.ID' (interface.ok si) hs csm ∗
      (nodeFounder γ N vs cv.ID' ∨
        (nodeJoin γ N cv.ID' ∗ confAt γ 0 (Membership.simple (GMap.listToSet vs)) ∗ ⌜vs.Nodup⌝)) }}
    (App (Val #(functions RestartNode [])) (Val #c))
  {{ (nd : GoInterface), RET #nd;
      ∃ (n : Loc), ⌜nd = interface.mkOk (go.GoType.PointerType node.ty) #n⌝ ∗
        isNode n γ N cv.ID' ∗ nodeDriver n γ N (NodeDriverState.init (interface.ok si)) ∗
        nodeConfig n γ N ⟨0, Membership.simple (GMap.listToSet vs)⟩ ∗
        -- (2026-10-29, stage U9a) the node runs (`node.Stop` takes it whole)
        nodeRunning n γ N 1 }}

end spec

end EtcdGrove
end Perennial
