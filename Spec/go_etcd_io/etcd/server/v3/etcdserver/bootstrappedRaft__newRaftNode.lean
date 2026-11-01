/-
`(*bootstrappedRaft).newRaftNode(ss, wal, cl)` (`bootstrap.go:578`): the new cluster's raft node
and its wrapper (stage R8b-C of the raft v3.7 retarget, 2026-10-16; D12). Lean-first (no Rocq
counterpart); see `InvNodeStart.lean`.

**The path.** With `b.peers` non-empty -- the new cluster's path, `bootstrapRaftFromCluster`;
`RestartNode`'s branch (`len(b.peers) == 0`: a member joining an existing cluster, or a restart
from a WAL) is out of scope and dead under the premise -- it calls `raft.StartNode(b.config,
b.peers)` (`StartNode.spec`: raft's `Bootstrap` of the peers' conf-change entries at term 1),
stores the node's `Status` method value in the package global `raftStatus` under `raftStatusMu`
(a contract on the globals, `rnRaftStatusOk`), and returns `newRaftNode` of the config built
from `b` (`lg`, `heartbeat`, `raftStorage = b.storage`), the node, the WAL
(`serverstorage.NewStorage(b.lg, wal, ss)`, a contract: `isRNWal`) and the closure `isIDRemoved`
over `cl.IsIDRemoved` (a contract on the cluster: `isRNIDRemoved`).

**The premises on `b.config`** are `StartNode.spec`'s (`NewRawNode`'s on a new cluster's
config, the storage `b.storage` a fresh `MemoryStorage`: `NewMemoryStorage`'s `memStorEmpty`, as
raft's `ownStorage (memStorIface ms)` under the `MemoryStorage` instance, which the composition
holds with the registry; raft owns it from the call on). `PreVote` and `CheckQuorum` either way
since 2026-10-17 (notes/STATUS.md, "Raft: CheckQuorum and PreVote on"; until then both were
required `false`, D12: etcd's `raftConfig` sets both). The `InitialState` closure premise is `StartNode.spec`'s
(D7's shape; a fresh `MemoryStorage`'s conf state is empty); since D17d (2026-10-18) it borrows the
application's snapshot token (`memSnapTok`), which the call takes and gives back.

**The ghost state** is the cluster's, allocated before (2026-10-27: the node API's
`cluster_alloc`/`dynamicCluster_alloc`): this node's boot token (`nodeBoot`/`nodeDynamicBoot`), the
storage's certificate link (a static cluster) or its cap (a dynamic one), as `StartNode` takes them.

**The post**: the node API's (`isNode`, `nodeDriver` at its start, in a dynamic cluster
`nodeConfig` at the peers' membership), and the wrapper as `newRaftNode`
leaves it (`rnBuilt`, over the config built here: the closure meets `isRNIDRemoved`, the WAL
`isRNWal`; `transport` nil, owned) with the wrapper's names tied to the node's (`node`, `id`,
`nl`, `ms = b.storage`, `γs`, `reg`, and `pre` the caller's). The receiver and the peers' slice
come back at their fraction.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvNodeStart

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- See the file header. (2026-10-27: over raft's node API, at the cluster's storage model,
`srvStor`.) -/
abbrev bootstrappedRaft.newRaftNode.spec : Prop :=
  ∀ (E : RNEnv GF) (γr : SrvRaft) (b ss wal cl : Loc) (dq : DFrac)
    (bv : bootstrappedRaft) (cv : Config) (lok : GoInterfaceOk) (γs : MemStorNames)
    (pre : List EntryModel)
    (pv : List Peer) (ps : List w64) (ctxs : List (List w8)) (Q : IProp GF),
  letI := srvStor (GF := GF) γr
  -- `newRaftNode`'s premises: a logger, a heartbeat
  bv.lg' ≠ null →
  bv.heartbeat' ≠ W64 0 →
  -- `NewRawNode`'s premises on `b.config` (`StartNode.spec`'s; the storage `b.storage`, a
  -- `MemoryStorage`); `CheckQuorum` and `PreVote` either way since 2026-10-17
  ConfigValid cv →
  cv.Logger' = interface.ok lok →
  cv.Storage' = memStorIface bv.storage' →
  sint.Z cv.MaxInflightMsgs' < 2 ^ 62 →
  cv.DisableProposalForwarding' = false →
  cv.ReadOnlyOption' = W64 0 →
  cv.DisableConfChangeValidation' = false →
  (cv.MaxCommittedSizePerReady' ≠ W64 0 ∨ cv.MaxSizePerMsg' ≠ W64 0) →
  cv.AsyncStorageWrites' = false →
  cv.Applied' = W64 0 →
  -- the peers: their ids `ps`, distinct and non-zero, this node among them, the cluster's voters
  ps = pv.map Peer.ID' →
  ps ≠ [] → ps.Nodup → W64 0 ∉ ps →
  (ps.length : Int) ≤ 2 ^ 62 →
  cv.ID' ∈ ps →
  γr.vs = ps →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      "Hb" ∷ b ↦{dq} bv ∗ "Hc" ∷ bv.config' ↦ cv ∗ "#Hlok" ∷ isLogger lok ∗
      -- (2026-10-30, the repair: raft's unified `StartNode.spec`) the storage `b.storage` as
      -- `StartNode` boots it (`bootStorage` at the zero hard state and the empty conf state, with
      -- the frame `Q` its `InitialState`'s update gives: for the server `srvMem_bootStorage`'s)
      "Hbs" ∷ bootStorage γr.cl cv.ID' (memStorIface bv.storage')
        (HardStateM.mk (W64 0) (W64 0) (W64 0)) memSnapEmpty.Metadata'.ConfState' Q ∗
      -- the peers and their contexts
      "Hpeers" ∷ bv.peers' ↦*{dq} pv ∗ "#Hctx" ∷ peersCtx pv ctxs ∗
      -- this node's boot token (the cluster's allocation's)
      "Hboot" ∷ nodeBoot γr.cl srvClusterN ps ctxs cv.ID' ∗
      -- the contracts (`InvNodeStart.lean`)
      "#Hzap" ∷ rnLoggerZapOk ∗ "#Hsetlg" ∷ rnSetLoggerOk ∗ "#Htdok" ∷ rnTimeoutDetectorOk ∗
      "#Htkok" ∷ rnTickerOk E ∗ "#Hrs" ∷ rnRaftStatusOk ∗ "#Hns" ∷ rnNewStorageOk ∗
      "#Hcl" ∷ rnClusterOk cl }}
    (App (App (App (Val (b @!! go.GoType.PointerType bootstrappedRaft.ty @!! go!"newRaftNode"))
      (Val #ss)) (Val #wal)) (Val #cl))
  {{ (r : Loc), RET #r;
      ∃ (n : Loc) (γw : RNNames) (f : GoFunc) (st : GoInterface),
        ⌜γw.node = γr ∧ γw.id = cv.ID' ∧ γw.nl = n ∧ γw.pre = pre ∧ γw.ms = bv.storage' ∧
          γw.γs = γs⌝ ∗
        -- the node API's node
        isNode n γr.cl srvClusterN cv.ID' ∗
        nodeDriver n γr.cl srvClusterN (NodeDriverState.init (memStorIface bv.storage')) ∗
        nodeConfig n γr.cl srvClusterN ⟨0, Membership.simple (GMap.listToSet ps)⟩ ∗
        -- (2026-10-30, the repair) the node's whole running token (`StartNode`'s)
        nodeRunning n γr.cl srvClusterN 1 ∗
        -- the wrapper, over the config built here
        isRNIDRemoved f ∗ isRNWal st ∗
        -- (D22 J1a, 2026-10-26) a `*storage` over the snapshotter `ss` (`rnNewStorageOk`'s)
        ⌜rnStorageOf st ss⌝ ∗
        rnBuilt E γw r
          (raftNodeConfig.mk bv.lg' f (interface.mkOk (go.GoType.PointerType node.ty) #n)
            bv.storage' st bv.heartbeat' GoInterface.nil) ∗
        -- (2026-10-27) the peers' slice not back: the node API's `StartNode` keeps it (proposed:
        -- give it back, it only reads it)
        b ↦{dq} bv ∗
        -- (2026-10-30, the repair) the storage's frame (`InitialState` ran before the node's
        -- goroutine)
        Q }}

end spec

end EtcdGrove
end Perennial
