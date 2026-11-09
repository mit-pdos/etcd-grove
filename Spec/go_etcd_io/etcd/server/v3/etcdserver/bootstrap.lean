/-
## `bootstrap(cfg)` (`bootstrap.go:53-125`): **trusted** (names only)

**Users.** `NewServer` (`server.go:296`) only.

**Why it is true of Go** (each path of `bootstrap.go`): it creates the data, member and snapshot
directories, opens (or creates) the backend at `BackendPath()` (`OpenBackend`, which panics if bbolt
cannot open it: `diskOk`), and then by the WAL directory's existence (`wal.Exist`):
* **no WAL, new cluster** (`memberStart_new`: a fresh directory, `NewCluster`): the members from
  the initial-cluster map (`NewClusterFromURLsMap`: an error on two equal ids or an id `0`, so a
  boot token of an allocation whose ids are not distinct is never used), the member by name; a
  new WAL with the node and cluster ids (`wal.Create`: `Recs.init`, a panic on failure: `diskOk`);
  the raft record with every member as a peer (`StartNode`'s bootstrap log, the JSON of each
  member as its context: the boot token's raft resources). `isMemberBootstrapped` asks the peers
  over HTTP whether this member already started: an error if one says so (trusted: the peers'
  answers are those of `γ`'s members).
* **no WAL, existing cluster** (`memberStart_join`): the cluster from the peers
  (`GetClusterFromRemotePeers`, a GET of `/members` at the initial cluster's other peer URLs), the
  member's id assigned by its peer URLs (`ValidateClusterAndAssignIDs`: an error unless the local
  and remote URL sets match one to one), no peers for raft (`RestartNode` from an empty storage);
  the join right's reserved vacancy of the id added under its URLs (single-use URL sets: no other
  member can hold them). **Trusted, and where the trust lies**: a `2xx` answer to `/members` at a
  reserved peer address of `γ` is a list of `γ`'s members at a state the cluster reached. True of
  every protocol a program can serve there today: `raftCompat` protocols (this repository's
  starters, `Rafthttp.raftProto`) answer `/members` with `404`, so `bootstrap` errors and a join
  through them fails (`ReqJoin`'s error branch). etcd's own peer handler (`etcdhttp.NewPeerHandler`,
  untranslated) answers from the member's applied view: a program serving it needs that handler's
  spec (open: `batch-2e.md` Q8).
* **a WAL** (`memberStart_restart`: `memberDisk`): the newest valid snapshot record
  (`Wal.Recs.newest`), the backend recovered from the snapshot db if the backend is behind it
  (`RecoverSnapshotBackend`, which renames `<snap>.snap.db` onto the backend's path: the image
  `Snap.snapDbs` held), the WAL opened at that record and read whole (`ReadAll`: `Recs.entsAfter`,
  `Recs.hs`; a torn tail repaired once: `wal.Repair`), the member and cluster ids from the
  metadata, the cluster's view recovered from the backend (`RaftCluster.Recover`), the snapshot's
  configuration rebuilt from the backend's members (`buildConfStateFromV3store`), a
  `MemoryStorage` of the snapshot, the hard state and the entries (`StorageHolds` of the durable
  state `memberDisk` holds), raft's record with no peers.
The result `bootOk b γ id cfg` has one sealed part per subsystem (`ApiBoot.lean`).

**Changes** (from the old `bootstrapContract`/`bootOk`/`bootOkR`, a premise of `NewServer.spec`
until R1-4: the whole-`bootOk` review): one trusted triple for the three starts (the old one covered
a new cluster's first start only, `bootOkR` a restart at `σ.b = 0`: R2d'a); no write-back budget
(`N + 7 + bootWB ≤ wbInit`: the backend's bounds are 4a's); the first-start configuration premises
(`bootCfgFresh`) are the start right's; no `Hclose` (the closers' own specs, R-D1).

**Margin.** `ForceNewCluster` (excluded by `memberStart_restart`), discovery (`ShouldDiscover`: the
initial cluster from a discovery service; `bootCfgOk`'s old exclusion, kept: Q4 of the report),
bootstrap defragmentation (`BootstrapDefragThresholdMegabytes`: the backend's `Defrag` keeps its
image: 4a's spec) are inside the configurations the premises admit or excluded as said.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot
public import Spec.go_uber_org.zap.Api
public import Spec.go_etcd_io.etcd.server.v3.features.Api
public import Spec.go_etcd_io.etcd.server.v3.storage.Api

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

/-- **`bootstrap(cfg)`** (trusted): the opened storage, cluster view and raft record of the member
the start right names, or an error. -/
def bootstrap.spec : Prop :=
  ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (c : Config.Model) (γ : Cluster)
    (oid : Option Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ Config.cfgHeap cfg c ∗ Zap.isLogger cfg.Logger' ∗
      Features.serverGate cfg.ServerFeatureGate' ∗ ⌜ServerStorage.diskOk⌝ ∗
      ⌜raftNodeBootCfg cfg⌝ ∗ backendBootRes cfg ∗ memberStart γ cfg c oid }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.bootstrap)) (Val #cfg))
  {{ (b : Loc) (err : GoInterface), RET (PairV #b #err);
      ⌜b = null ∧ err ≠ GoInterface.nil⌝ ∨
      ⌜err = GoInterface.nil⌝ ∗ ∃ id : Nat, ⌜0 < id ∧ id < 2 ^ 64 ∧ ∀ i, oid = some i → id = i⌝ ∗
        bootOk b γ id cfg }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
