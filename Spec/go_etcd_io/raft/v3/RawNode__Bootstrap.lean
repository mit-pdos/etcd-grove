/- Lean-first (no Rocq counterpart).

## `RawNode.Bootstrap(peers)` (bootstrap.go:32): a new cluster's initial log

On a node `NewRawNode` just built on an empty storage with an empty conf state (`rawNodeFresh`
at no voter, `InvBoot.lean`), for the peers `peers` (at least one; `len(peers) == 0` and a
non-empty storage are the two error returns, excluded): `rn.prevHardSt = emptyState` (so the
first `Ready` carries the hard state), `becomeFollower(1, None)`, one `EntryConfChange` per peer
(`{Type: AddNode, NodeId: peer.ID, Context: peer.Context}` marshalled, at term `1`, index `i + 1`)
appended to the log, `raftLog.committed = len(peers)` (the raw store: the entries are committed
although unstable, D12), then `applyConfChange((&pb.ConfChange{NodeId: peer.ID, Type:
AddNode}).AsV2())` per peer, which installs the peers as the voters with fresh `Progress`
(`Next = max(lastIndex, 1) = n`, `Match = 0`). Nothing is applied (`applied = applying = 0`): the
application sees the conf changes through the first `Ready` (`StartNode.spec`).

The result is the node closed, `ownRawNode` in the mode `md` at the peers' configuration, with
the delivered log empty, the term `1`, and the ghost state of the bootstrap state (`bootInit γ md
id V bootLog`, allocated before the call: statically `ownRaftGhost γ id (bootPState bootLog)`,
`ownRaftGhost_alloc_boot`; dynamically, since 2026-10-25, T-M M2a, the dynamic model's `rboot c0
bootLog` at the configuration index `0`, `raft_dyn_alloc_boot`), which the physical state refines:
a follower at term `1`, the log `bootLog` from the empty base, committed through it.

The premises are `StartNode.spec`'s on the peers and the bootstrap log (`BootLogOk ps
bootLog`: entry `k` is the `k`-th peer's, which fixes the terms, indices and types the code
writes), and `bootMarshal` ties `proto.Marshal`'s bytes to `bootLog[k].Data'` (protobuf's
determinism at these inputs, a trust-boundary premise discharged where the node is composed;
`InvBoot.lean`). `isCommitted γ bootLog` gives the empty delivered log's `isCommitted γ []`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvBoot

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

/-- See the file header. -/
abbrev RawNode.Bootstrap.spec : Prop :=
  ∀ (γ : RaftNames) (md : RNMode) (rn : Loc) (id : w64) (si : GoInterfaceOk) (sdr pre : Bool)
    (s : NState)
    (peers : GoSlice) (dq : DFrac) (pv : List Peer) (ps : List w64) (ctxs : List (List w8))
    (bootLog : List EntryM),
  -- the peers: their ids `ps`, distinct and non-zero, this node among them, the cluster
  ps = pv.map Peer.ID' →
  ps ≠ [] → ps.Nodup → W64 0 ∉ ps →
  (ps.length : Int) ≤ 2 ^ 62 →
  id ∈ ps →
  γ.reCfg = GMap.listToSet ps →
  -- the bootstrap log, the ghost state's
  γ.reBoot = bootLog →
  BootLogOk ps bootLog →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      -- the node `NewRawNode` built on an empty conf state, open
      rawNodeFresh rn id si ∅ sdr pre s ∗
      -- the peers, their contexts, and `Marshal` at their conf changes (`InvBoot.lean`)
      peers ↦*{dq} pv ∗ peersCtx pv ctxs ∗ bootMarshal ps ctxs bootLog ∗
      -- this node's ghost state at the bootstrap state in the mode `md` (2026-10-25, T-M M2a;
      -- until then static), and the committed boot log
      bootInit γ md id (GMap.listToSet ps) bootLog ∗ isCommitted γ bootLog ∗
      -- (2026-10-19, D21 M3) in the cluster's no-snapshot mode, a storage that never compacts
      -- past index `1`
      NsCap γ.reNoSnap (interface.ok si) ∗
      -- (D22 S-b′3, 2026-10-20) the storage's certificate link (`certLink`: none needed in the
      -- no-snapshot mode)
      certLink γ (interface.ok si) }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"Bootstrap")) (Val #peers))
  {{ (err : GoInterface), RET #err;
      ⌜err = interface.nil⌝ ∗
      ownRawNode γ rn id
        { delivered := [], unpersisted := [], steps := [], term := W64 1,
          storage := interface.ok si, mode := md,
          cfg := cfgState (GMap.listToSet ps) ∅, tc := W64 1 } ∗
      peers ↦*{dq} pv }}

end spec

end EtcdGrove
end Perennial
