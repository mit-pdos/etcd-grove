/-
## `bootstrap(cfg)` (`bootstrap.go:53-125`): **trusted** (names only)

**Users.** `NewServer` (`server.go:296`) only.

**Why it is true of Go** (each path of `bootstrap.go`): it creates the data, member and snapshot
directories, opens (or creates) the backend at `BackendPath()` (`OpenBackend`, which panics if bbolt
cannot open it: `diskOk`), and then by the WAL directory's existence (`wal.Exist`):
* **no WAL, new cluster** (a disk of kind `.boot ms m`: a fresh directory, `NewCluster`): the members from
  the initial-cluster map (`NewClusterFromURLsMap`: an error on two equal ids or an id `0`, so a
  boot token of an allocation whose ids are not distinct is never used), the member by name; a
  new WAL with the node and cluster ids (`wal.Create`: `Recs.init`, a panic on failure: `diskOk`);
  the raft record with every member as a peer (`StartNode`'s bootstrap log, the JSON of each
  member as its context: the boot token's raft resources). `isMemberBootstrapped` asks the peers
  over HTTP whether this member already started: an error if one says so (trusted: the peers'
  answers are those of `γ`'s members).
* **no WAL, existing cluster** (a disk of kind `.join urls`): the cluster from the peers
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
* **a WAL** (a disk of kind `.member id`, after a stop or a crash: `disk_crash`): the newest valid snapshot record
  (`Wal.Recs.newest`), the backend recovered from the snapshot db if the backend is behind it
  (`RecoverSnapshotBackend`, which renames `<snap>.snap.db` onto the backend's path: the image
  `Snap.snapDbs` held), the WAL opened at that record and read whole (`ReadAll`: `Recs.entsAfter`,
  `Recs.hs`; a torn tail repaired once: `wal.Repair`), the member and cluster ids from the
  metadata, the cluster's view recovered from the backend (`RaftCluster.Recover`), the snapshot's
  configuration rebuilt from the backend's members (`buildConfStateFromV3store`), a
  `MemoryStorage` of the snapshot, the hard state and the entries (`StorageHolds` of the durable
  state `memberDisk` holds), raft's record with no peers. This includes a WAL at `Recs.init md`, left
  by a crash inside `wal.Create` after its rename (`Wal.walCreating_crash`): the zero snapshot record,
  no entries, a backend at index `0` (nothing to recover), `RestartNode` from an empty storage with
  the configuration the backend holds (third crash pass, F2-crash N2).
The result `bootOk b γ id cfg` has one sealed part per subsystem (`ApiBoot.lean`).

**Crashes inside `bootstrap`** (verify round, crash pass: R-A8 N4; trusted, as the rest): every
durable change is made through `memberStart`'s `diskAcc`, at its atomic point, so that `diskState`
describes the directories at every step and `disk_crash` holds of a crash at any point: the
directories' creation (nothing of `diskState`'s), the backend's open (4a's `New`: the file closed
until the open, then the open file's history, swapped at bbolt's open by 4a's `beOpenUpd`, fired
inside `diskAcc`: repair3-boot, no window left), `RecoverSnapshotBackend`'s rename (`Snap.dbFile_rename`'s update, the revert list and the snapshot
directory's rename record `Snap.snapRen`, third crash pass, F2-crash N1),
`wal.Create` (a temporary directory renamed onto the WAL's path, `wal.go:185`, the parent fsynced
before it returns, `:225`: the disk, still `.boot`/`.join`, holds `Wal.walCreating wd md` from the
rename's access to the fsync's, where the kind moves to `.member id` with `Wal.walRecs wd (Recs.init
md)`; a crash in between gives the WAL at `Recs.init md` or no WAL, `Wal.walCreating_crash`, and
`disk_crash`'s kind `.member id` or the old one: third crash pass, F2-crash N2, which found this text
and `ApiBoot`'s disagreeing on where the kind moves), `wal.Repair` (a torn tail
truncated: `walRecs` is what `ReadAll` returns, which the tail never was part of). The WAL replay
reads only.

**Changes** (from the old `bootstrapContract`/`bootOk`/`bootOkR`, a premise of `NewServer.spec`
until R1-4: the whole-`bootOk` review): one trusted triple for the three starts (the old one covered
a new cluster's first start only, `bootOkR` a restart at `σ.b = 0`: R2d'a); no write-back budget
(`N + 7 + bootWB ≤ wbInit`: the backend's bounds are 4a's); the first-start configuration premises
(`bootCfgFresh`) are the start right's; no `Hclose` (the closers' own specs, R-D1).

**Margin.** `ForceNewCluster` (excluded by `diskCfgOk`), discovery (`ShouldDiscover`: the
initial cluster from a discovery service; `bootCfgOk`'s old exclusion, kept: Q4 of the report),
bootstrap defragmentation (`BootstrapDefragThresholdMegabytes`: the backend's `Defrag` keeps its
image: 4a's spec) are inside the configurations the premises admit or excluded as said.

Changes: verify-round (server-boot's request): `OpenBackend` returns 4a's `isBackend` through the allocation step, its hook contract `Backend.hookOk` from cindex's `UnsafeSave` (cindex/Api's header), with premises `backendBootRes` (now `Backend.envOk` and the quota, `MemoryMlock = false`), `safeRegOk`, `threadTok`; the snapshot directory's invariant is allocated with `Snap.snapGone sd H` beside `snapDbs` at `(fun _ _ => False)`.

Changes: verify-round (third crash pass, F2-crash N1, N2; trusted text only, statement unchanged):
the snapshot directory's invariant is allocated with `Snap.snapRen sd none` beside `snapGone`; the
WAL's creation holds `Wal.walCreating` between its rename and its parent's fsync, and the kind moves
at the fsync; the WAL path covers a WAL at `Recs.init`.

Changes: verify-round, last relay (server-boot's request): the opener gets the backend file's `Backend.beNoRevert` (4a's `beFile_of`/`beFile_none` give it with the file), kept in `diskState`'s realization for `applySnapshot`'s `OpenSnapshotBackend`.
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
