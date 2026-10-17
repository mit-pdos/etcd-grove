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
holds with the registry; raft owns it from the call on). **Among them `CheckQuorum = false` and `PreVote = false`: etcd's
`raftConfig` (`bootstrap.go`) sets `CheckQuorum: true` and `PreVote` on by default, so this
theorem does not cover etcd's own configuration** (`MsgCheckQuorum` and pre-vote are out of the
model's scope: the user's decision, D12). The `InitialState` closure premise is `StartNode.spec`'s
(D7's shape; a fresh `MemoryStorage`'s conf state is empty).

**The ghost state** is the cluster's, allocated before (`ownRaftGhost_alloc_boot`): this node's
`ownRaftGhost γ cv.ID' (bootPState bootLog)` and `isCommitted γ bootLog`, with `γ.reBoot =
bootLog` and `BootLogOk γ.reCCOk ps bootLog`; the peers' contexts and the `Marshal` premise
(`bootMarshal`, `InvBoot.lean`) as `StartNode.spec` takes them. The budget is the cluster's, at
least at the bootstrap term `1`.

**The post**: raft's (`isNode`, `nodeDriver` at `[]`, `nodeCfg` at the peers' configuration, the
names tied: static mode, the storage `memStorIface b.storage`), and the wrapper as `newRaftNode`
leaves it (`rnBuilt`, over the config built here: the closure meets `isRNIDRemoved`, the WAL
`isRNWal`; `transport` nil, owned) with the wrapper's names tied to the node's (`node`, `id`,
`nl`, `ms = b.storage`, `γs`, `reg`, and `pre` the caller's). The receiver and the peers' slice
come back at their fraction.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvNodeStart
public import Spec.go_etcd_io.raft.v3.StartNode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- See the file header. (Stated over raft's `StorageModel`, as raft's `StartNode.spec` is; the
composition instantiates it with the `MemoryStorage`'s, `memStorageModel` under `MemStorReg
⟨reg⟩`.) -/
abbrev bootstrappedRaft.newRaftNode.spec : Prop :=
  ∀ (E : RNEnv GF) (γ : RaftNames) (bud : BudgetNames) (b ss wal cl : Loc) (dq : DFrac)
    (bv : bootstrappedRaft) (cv : Config) (lok : GoInterfaceOk) (γs : MemStorNames) (reg : GName)
    (pre : List EntryModel)
    (pv : List Peer) (ps : List w64) (ctxs : List (List w8)) (bootLog : List EntryM),
  -- `newRaftNode`'s premises: a logger, a heartbeat
  bv.lg' ≠ null →
  bv.heartbeat' ≠ W64 0 →
  -- `NewRawNode`'s premises on `b.config` (`StartNode.spec`'s; the storage `b.storage`, a
  -- `MemoryStorage`); **`CheckQuorum` and `PreVote` off: not etcd's own configuration**
  ConfigValid cv →
  cv.Logger' = interface.ok lok →
  cv.Storage' = memStorIface bv.storage' →
  sint.Z cv.MaxInflightMsgs' < 2 ^ 62 →
  cv.CheckQuorum' = false →
  cv.DisableProposalForwarding' = false →
  -- (PR raft#88) no proposal-forwarding callback (etcd sets none)
  cv.DisableProposalForwardingCallback' = func.nil →
  cv.ReadOnlyOption' = W64 0 →
  cv.DisableConfChangeValidation' = false →
  (cv.MaxCommittedSizePerReady' ≠ W64 0 ∨ cv.MaxSizePerMsg' ≠ W64 0) →
  cv.AsyncStorageWrites' = false →
  cv.PreVote' = false →
  cv.Applied' = W64 0 →
  -- the peers: their ids `ps`, distinct and non-zero, this node among them, the cluster
  ps = pv.map Peer.ID' →
  ps ≠ [] → ps.Nodup → W64 0 ∉ ps →
  (ps.length : Int) ≤ 2 ^ 62 →
  cv.ID' ∈ ps →
  γ.reCfg = GMap.listToSet ps →
  -- the bootstrap log, the ghost state's
  γ.reBoot = bootLog →
  BootLogOk γ.reCCOk ps bootLog →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      "Hb" ∷ b ↦{dq} bv ∗ "Hc" ∷ bv.config' ↦ cv ∗ "#Hlok" ∷ isLogger lok ∗
      -- the fresh `MemoryStorage` `b.storage` as raft's `Storage` (`memOwnStorage_empty`,
      -- `memStorage_isStorage`, over the registry the composition holds)
      "#Hsi" ∷ isStorage (memStorIface bv.storage') ∗
      "Hsto" ∷ ownStorage (memStorIface bv.storage') memStorEmpty ∗
      -- `StartNode.spec`'s `InitialState` premise (D7's shape; the conf state empty)
      "#Hinit" ∷ □ (∀ (Φ : val → IProp GF) (ss' : entryID),
           ownStorage (memStorIface bv.storage') { memStorEmpty with ss := ss' } -∗
           (∀ (hp cs : Loc) (al : Bool),
            ownStorage (memStorIface bv.storage') { memStorEmpty with ss := ss' } -∗
            hsOpt hp (HardStateM.mk (W64 0) (W64 0) (W64 0)) -∗
            csPts cs DFrac.discard (ConfStateM.mk [] [] [] [] false) al -∗
            Φ (PairV (PairV #hp #cs) #interface.nil)) -∗
           WP (App (Val #(methods (go.GoType.PointerType MemoryStorage.ty) go!"InitialState" #bv.storage'))
             (Val #())) {{ Φ }}) ∗
      -- the peers, their contexts, and `Marshal` at their conf changes
      "Hpeers" ∷ bv.peers' ↦*{dq} pv ∗ "#Hctx" ∷ peersCtx pv ctxs ∗
      "#Hmarshal" ∷ bootMarshal ps ctxs bootLog ∗
      -- this node's ghost state at the bootstrap state, and the committed boot log
      "Hghost" ∷ ownRaftGhost γ cv.ID' (bootPState bootLog) ∗ "#Hcomm" ∷ isCommitted γ bootLog ∗
      -- the cluster's term budget, at least at the bootstrap term `1` (`StartNode.spec`'s)
      "#Hbud" ∷ inv budgetN (budgetInv bud) ∗ "#HtermLB" ∷ termLB bud (W64 1) ∗
      -- the contracts (`InvNodeStart.lean`)
      "#Hzap" ∷ rnLoggerZapOk ∗ "#Hsetlg" ∷ rnSetLoggerOk ∗ "#Htdok" ∷ rnTimeoutDetectorOk ∗
      "#Htkok" ∷ rnTickerOk E ∗ "#Hrs" ∷ rnRaftStatusOk ∗ "#Hns" ∷ rnNewStorageOk ∗
      "#Hcl" ∷ rnClusterOk cl }}
    (App (App (App (Val (b @!! go.GoType.PointerType bootstrappedRaft.ty @!! go!"newRaftNode"))
      (Val #ss)) (Val #wal)) (Val #cl))
  {{ (r : Loc), RET #r;
      ∃ (γn : NodeNames) (n : Loc) (γw : RNNames) (f : GoFunc) (st : GoInterface),
        ⌜γn.raft = γ ∧ γn.bud = bud ∧ γn.stor = memStorIface bv.storage' ∧
          γn.mode = RNMode.static ∧
          γw.node = γn ∧ γw.id = cv.ID' ∧ γw.nl = n ∧ γw.pre = pre ∧ γw.ms = bv.storage' ∧
          γw.γs = γs ∧ γw.reg = reg⌝ ∗
        -- raft's node
        isNode γn cv.ID' n ∗ nodeDriver γn cv.ID' n [] ∗
        nodeCfg γn 0 (cfgState (GMap.listToSet ps) ∅) ∗
        -- the wrapper, over the config built here
        isRNIDRemoved f ∗ isRNWal st ∗
        rnBuilt E γw r
          (raftNodeConfig.mk bv.lg' f (interface.mkOk (go.GoType.PointerType node.ty) #n)
            bv.storage' st bv.heartbeat' GoInterface.nil) ∗
        b ↦{dq} bv ∗ bv.peers' ↦*{dq} pv }}

end spec

end EtcdGrove
end Perennial
