/-
## `(*bootstrappedRaft).newRaftNode(ss, wal, cl)` (`bootstrap.go:568-591`)

**Users.** `NewServer` (`server.go:319`), once.

**Proof sketch.** `bootRaftOk br γ id cfg` holds the record's configuration (a validating
`raft.Config` over the record's `MemoryStorage`, `raftNodeBootCfg`), its peers and what raft's
start takes: with peers (a new member) `Raft.StartNode.spec` (the boot token's `raftState γ.raft id
Durable.init`, `nodeVacant`, the bootstrap log); without (a joiner or a restart)
`Raft.RestartNode.spec` (the durable state the storage holds, `StorageHolds`, the configuration at
the backend's consistent index: R1's restart at any committed `a`). The package's status variable
under `raftStatusMu` (the package's init law: 2d). `ServerStorage.NewStorage.spec` (the opened WAL,
the snapshotter: `isStorage st wd sd` and the whole `storageOpen st 1`), then 2d's `newRaftNode`
(the ticker at the positive heartbeat): `raftNodeBuilt rn γ id st`.

**Changes** (from `specs-ref`'s `bootstrappedRaft__newRaftNode.lean`, `StartNode` only: a first
start): both starts.

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot
public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **Starts the member's raft node** (`StartNode` or `RestartNode`) over the opened WAL. -/
def bootstrappedRaft.newRaftNode.spec : Prop :=
  ∀ (br : Loc) (γ : Cluster) (id : Nat) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (ss : Loc) (sd : GoString) (w : Loc) (wd : GoString) (cl : Loc) (γc : Membership.CNames)
    (cid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ bootRaftOk br γ id cfg ∗ Snap.isSnapshotter ss sd ∗ Wal.walOpen w wd ∗
      Membership.isCluster cl γc cid (W64 id) }}
    (App (App (App (Val (br @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.bootstrappedRaft.ty @!! go!"newRaftNode")) (Val #ss)) (Val #w)) (Val #cl))
  {{ (rn : Loc), RET #rn; ∃ st : Loc, raftNodeBuilt rn γ id st ∗
      ServerStorage.isStorage st wd sd }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
