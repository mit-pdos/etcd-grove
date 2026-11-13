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

**The premises** (2026-11-05, rewritten from the spec's text: the paragraphs they replace named the
storage tokens, the `InitialState` closure and the static/dynamic boot tokens of before the node
API's unified `StartNode.spec`): the configuration and the peers (`rnStartCfg`: the wrapper's
logger, `NewRawNode`'s premises on `b.config` with `b.storage` its `MemoryStorage`, `PreVote` and
`CheckQuorum` either way since 2026-10-17; the peers non-empty with their ids `ps`), a positive
heartbeat (`newRaftNode`'s, a scope restriction), the WAL read (`NewStorage`'s contract); the
receiver and `b.config`, the logger; the storage as `StartNode` boots it (`restartStorage` at the
empty contents, the zero hard state and the empty conf state, with the frame `Q` its
`InitialState`'s continuation gives at the storage's key: the server's from `srvMem_bootStorage`);
the peers and their contexts; the cluster's allocation for this node, allocated before (raft's
`cluster_alloc`): its boot token `nodeBoot`, its id vacant (`nodeVacant`) and its durable state at
`RaftState.init` (`raftState`); and the contracts (`InvNodeStart.lean`).

**The post**: the node API's (`isNode`, `nodeDriver` at its start at the storage's key `γw.key`,
`raftState` unchanged at `RaftState.init`, `nodeConfig` at the peers' membership, the whole
running token `nodeRunning 1`), and the wrapper as `newRaftNode` leaves it (`rnBuilt`, over the
config built here: the closure meets `isRNIDRemoved`, the storage `isWalStorage`, a `*storage`
over `ss` and the WAL `wal`; `transport` nil) with the wrapper's names tied to the node's (`node`,
`id`, `nl`, `ms = b.storage`, `γs`, the WAL's `wal`, and `pre` the caller's; `key` the storage's,
which `StartNode` names). The receiver and the peers' slice come back at their fraction
(`StartNode` only reads the peers), and the frame at the key, `Q γw.key`.
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
    (pre : List EntryModel) (ν : WalNames)
    (pv : List Peer) (ps : List w64) (ctxs : List (List w8)) (Q : GName → IProp GF),
  letI := srvStor (GF := GF) γr
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      -- the pure premises, one conjunction (2026-11-05, the user's M1: until then the
      -- configuration's, the peers' and the WAL's were implications before the triple): the
      -- configuration and the peers (`rnStartCfg`; 2026-11-05, the review's S: until then also the
      -- peers distinct, non-zero, at most `2 ^ 62`, this node among them and the cluster's voters,
      -- which nothing here uses), a positive heartbeat (`newRaftNode`'s: the final whole-`bootOk`
      -- review's S2, a scope restriction), and (2026-10-31, `notes/axiom-review/savesnap.md`) the
      -- WAL read (`NewStorage`'s contract)
      -- (2026-11-09, Q8 stage 0) and the cluster untraced (`cluster_alloc`'s): `StartNode`'s premise
      "%Hraft" ∷ ⌜rnStartCfg bv cv lok pv ps ∧ 0 < sint.Z bv.heartbeat' ∧ storage.walReady wal ∧
        Cluster.trace γr.cl = none⌝ ∗
      "Hb" ∷ b ↦{dq} bv ∗ "Hc" ∷ bv.config' ↦ cv ∗ "#Hlok" ∷ isLogger lok ∗
      -- (2026-10-30, the repair: raft's unified `StartNode.spec`) the storage `b.storage` as
      -- `StartNode` boots it (`restartStorage` at the empty contents: the zero hard state and the
      -- empty conf state, with the frame `Q` its `InitialState`'s continuation gives: for the
      -- server `srvMem_bootStorage`'s)
      "Hbs" ∷ restartStorage γr.cl (memStorIface bv.storage')
        ⟨HardStateM.mk (W64 0) (W64 0) (W64 0), none, entryID.mk (W64 0) (W64 0), []⟩
        memSnapEmpty.Metadata'.ConfState' 0 Q ∗
      -- the peers and their contexts
      "Hpeers" ∷ bv.peers' ↦*{dq} pv ∗ "#Hctx" ∷ peersCtx pv ctxs ∗
      -- this node's boot token (the cluster's allocation's, persistent), and (2026-11-01,
      -- durability layer 4: `StartNode`'s new premises) its id vacant and its durable state at
      -- `RaftState.init` (allocation's), over which `StartNode`'s update fires at once
      "Hboot" ∷ nodeBoot γr.cl srvClusterN ps ctxs cv.ID' ∗
      "Hvac" ∷ nodeVacant γr.cl cv.ID' ∗
      "Hrst" ∷ raftState γr.cl cv.ID' RaftState.init ∗
      -- the contracts (`InvNodeStart.lean`; 2026-11-03: `rnTickerOk E` gone, `newRaftNode`'s
      -- proof calls the ticker's spec)
      "#Hzap" ∷ rnLoggerZapOk ∗ "#Hsetlg" ∷ rnSetLoggerOk ∗ "#Htdok" ∷ rnTimeoutDetectorOk ∗
      "#Hrs" ∷ rnRaftStatusOk ∗ "#Hns" ∷ rnNewStorageOk ∗
      "#Hcl" ∷ rnClusterOk cl }}
    (App (App (App (Val (b @!! go.GoType.PointerType bootstrappedRaft.ty @!! go!"newRaftNode"))
      (Val #ss)) (Val #wal)) (Val #cl))
  {{ (r : Loc), RET #r;
      ∃ (n : Loc) (γw : RNNames) (f : GoFunc) (st : GoInterface),
        ⌜γw.node = γr ∧ γw.id = cv.ID' ∧ γw.nl = n ∧ γw.pre = pre ∧ γw.ms = bv.storage' ∧
          γw.γs = γs ∧ γw.wal = ν ∧ γw.a0 = [] ∧ γw.t0 = W64 0⌝ ∗
        -- the node API's node, its driver at the storage's key (the wrapper's, `γw.key`: raft
        -- names it at the attach), and (2026-11-01, durability layer 4) the node's durable state,
        -- unchanged by the update; (2026-11-05, the lease-expiry plan's E2 revision 5) made by
        -- `StartNode` (`nodeStartedFresh`)
        nodeStartedFresh n γr.cl srvClusterN ps ctxs cv.ID' ∗
        isNode n γr.cl srvClusterN cv.ID' ∗
        nodeDriver n γr.cl srvClusterN (NodeDriverState.init (memStorIface bv.storage') γw.key) ∗
        raftState γr.cl cv.ID' RaftState.init ∗
        nodeConfig n γr.cl srvClusterN ⟨0, Membership.simple (GMap.listToSet ps)⟩ ∗
        -- (2026-10-30, the repair) the node's whole running token (`StartNode`'s)
        nodeRunning n γr.cl srvClusterN 1 ∗
        -- the wrapper, over the config built here
        isRNIDRemoved f ∗ isWalStorage st ∗
        -- (D22 J1a, 2026-10-26) a `*storage` over the snapshotter `ss` (`rnNewStorageOk`'s); (2026-10-31)
        -- over the WAL `wal`
        ⌜rnStorageOf st ss ∧ storage.walOf st = wal⌝ ∗
        rnBuilt E γw r
          (raftNodeConfig.mk bv.lg' f (interface.mkOk (go.GoType.PointerType node.ty) #n)
            bv.storage' st bv.heartbeat' GoInterface.nil) ∗
        -- the receiver and (2026-11-05: until then kept, as the node API's `StartNode` did until
        -- it gave it back) the peers' slice
        b ↦{dq} bv ∗ bv.peers' ↦*{dq} pv ∗
        -- (2026-10-30, the repair) the storage's frame (`InitialState` ran before the node's
        -- goroutine), at the storage's key (2026-11-01, durability stage II (l): the frame depends
        -- on the key, as `restartStorage`'s, so that the storage's invariant allocated at the key
        -- comes back at the wrapper's `γw.key`)
        Q γw.key }}

end spec

end EtcdGrove
end Perennial
