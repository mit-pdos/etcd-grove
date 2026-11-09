/-
# A member's lifecycle: allocation, start, serving, stop, restart (batch 2e)

The vocabulary of `NewServer`, `Start`, `Stop`/`HardStop` and the cluster contract's start-up
part (`notes/specs-only/top.md`, K1-K3, K6; `req/go_etcd_io_etcd_server_v3_etcdserver.md`,
"from W0"). Namespace `EtcdServer`, shared with the request path (2c) and the apply thread (2d),
whose `Api.lean` modules import this one: `isServer` below is the handle their specs take.

## The shape, in words

**A cluster** is W0's `Cluster` (`api/v3/State.lean`). The program allocates its state with the
members it will start (`cluster_alloc`, K1): it gets `etcdState γ (State.init ms)` in full, one
`memberBoot γ ms m` per initial member, and `memberUrls γ U`, the peer-URL sets taken so far (the
initial members').

**A member's files** are keyed by its directories (`Config.Dirs`: the data directory and the
dedicated WAL directory, `Config.dirsOf cfg`). At program start a directory is `dataDirFresh ds`
(nothing of etcd's in it; the adequacy theorem's per-directory token: the paths pairwise distinct
for the whole run, canonical, no other string naming one of them: the axiom sweep's B3-1). A
stopped member's directory is `memberDisk γ id ds`: **its durable state, client-owned**; nothing
else is needed to start the member again on it.

**Starting a member** (`NewServer`, K2) takes the right to start a member of `γ` with
configuration `cfg`, `memberStart γ cfg c`, introduced in three ways, one law each:
* a member of a new cluster (`memberStart_new`): its `memberBoot` and a fresh directory, the
  configuration a new cluster's whose initial members are the allocated ones;
* a member added by a `MemberAdd` (`memberStart_join`): `memberJoin γ urls` for its peer URLs
  (from `memberUrls_take`: a peer-URL set is joined from a fresh directory at most once) and a
  fresh directory. **Keyed by the URLs, not the id**: `bootstrap` takes the id the cluster
  currently has for the configuration's peer URLs (`GetClusterFromRemotePeers`,
  `ValidateClusterAndAssignIDs`), which is not the id of an earlier `MemberAdd` if those URLs were
  removed and added again since; a token per id would let two processes run one id. With the
  token per URL set, the cluster's invariant reserves raft's vacancy for every id added under a
  pending URL set (etcd never commits an add of an id it has seen: `ErrIDRemoved`, `ErrIDExists`),
  and the joiner runs as whichever it finds. No `etcdLb` is needed: a member not in the cluster
  fails `bootstrap`'s validation (an error);
* a stopped member (`memberStart_restart`): its `memberDisk` (a WAL in the directory: etcd ignores
  `NewCluster` and replays it; any durable state, after snapshots and compactions).

and the environment's permission `envUpd γ ecfg` (W0's), the configuration's scope premises (one
sealed slot per subsystem, below) and the boundary resources (the logger, the feature gate, the
configuration's heap parts, the disk premise). It returns, for some member id `id`
(the restarted one's, the initial member's, the joined one's), `srvMember s γ id` (persistent: the
server object is member `id` of `γ`; `MemberID()` returns `id`) and `srvBuilt s γ id cfg`
(exclusive: built, not started).

**Starting it** (`Start`) turns `srvBuilt` into `isServer s γ` (persistent: the request path's
handle, what 2a's `v3rpc.Server` takes to register services that give `servesAt γ ep`, K3) and
`srvRunning s γ id ds` (exclusive: the right to stop it).

**Stopping it** (`HardStop`, `Stop`) takes `srvRunning` and gives back `memberDisk γ id ds`: the
closer returns what the goroutines it waits for held (`run`'s deferred shutdown: the scheduler,
the attached goroutines, the raft loop with its WAL, `Cleanup`'s stores and backend). `isServer`
stays: a request that reaches a stopped server is answered with an indefinite error (2c's
obligation, `req/go_etcd_io_etcd_server_v3_etcdserver.md`, "from 2e").

## Intended realization

* `Cluster` (W0's opaque type) holds, for the server batches, raft's cluster names (`Raft.Cluster`:
  the committed log, whose states are the model's, 2c/2d), the network's names (2f), and the
  id authority; `etcdState` is 2c/2d's (the committed log's state).
* `memberBoot γ ms m`: raft's `raftState γ.raft m.id Durable.init ∗ nodeVacant γ.raft m.id` from
  raft's `cluster_alloc` at the voters `ms`'s ids with the contexts `bootstrap` computes (the JSON of
  each member: `bootstrapRaftFromCluster`), and the boot log's `confDecided` facts. When the ids of
  `ms` are not distinct or include `0`, `bootstrap` fails for every member (`NewClusterFromURLsMap`):
  the allocation then gives tokens no start can use (a classical case split; no premise).
* `memberUrls γ U`: the authority of the reserved URL sets; `memberJoin γ urls`: its fragment,
  with which the cluster's invariant (it sees every committed `MemberAdd`) keeps, for each id added
  under `urls` while it is pending, `raftState γ.raft id Durable.init ∗ nodeVacant γ.raft id`
  (raft's `freshIds_take`: the ids an add commits are fresh).
* `memberDisk γ id ds` (the R2d'a lesson: every binder tied to the files, never a `∀` over states the
  files do not pin): `∃ R F img D ci, Wal.walRecs (walDirOf ds) R ∗ Snap.snapDbs (snapDirOf
  ds.dataDir) F ∗ Snap.beFile (backendPathOf ds.dataDir) (some img) ∗ raftState γ.raft id D ∗
  nodeVacant γ.raft id ∗ ⌜walHolds R D⌝ ∗ beHolds γ img ci ∗ ⌜R.readable⌝ ∗ …` where `walHolds R D`
  says the restart view of `R` (`R.newest`, `R.hs`, `R.entsAfter`) is `D`'s (raft's `StorageHolds`
  of the `MemoryStorage` `bootstrap` rebuilds), and `beHolds γ img ci` says the backend image is
  the KV state of the committed log's first `ci` entries with their configuration (`confAt γ.raft
  ci m` and the backend's member records), `ci` the image's consistent index. **`ci` is not bounded
  by the WAL's commit**: a stop after the apply thread ran ahead of the raft loop's last `Save` is
  bounded by the graceful stop's order (the loop finishes its iteration), but R1's restart takes
  `confAt` at any committed `a` (R1's round-1 F; `RestartNode.spec`), and 2d's replay applies
  only above `ci`. The snapshot record `bootstrap` reconstructs carries the backend's configuration at
  `ci`, not at its own index `si` (`bootstrap.go:107-115`; R1 provisability F3): raft's
  `snapValid` must admit it (`req/go_etcd_io_raft_v3.md`, "from 2e").
* `memberStart γ cfg c`: the disjunction of the three intro laws' left sides, at their pure
  conditions (each law is its injection; `NewServer`'s proof eliminates by cases inside the
  package).
* `srvMember s γ id`: read-only fields `memberID`, `r.transport` (2f's transport handle of member
  `id`), `cluster` (`Membership.isCluster`), `lgMu`/`lg`, `Cfg`.
* `srvBuilt s γ id cfg`: one conjunct per subsystem (the slot convention: `<sub>.srvInv`), each
  sealed by its owner: the raft node and its storage (2d: `newRaftNode`'s post; the WAL and the
  snapshotter's `ServerStorage.isStorage`, `Snap.isSnapshotter`), the backend with its hooks and
  the consistent index (4a, 2d), the lessor (3c), the KV store (3e), the auth store (3d), the
  alarm store (`V3alarm.isAlarmStore`), the compactor (`V3compactor.isCompactor` and its run token,
  when configured), the membership view (`Membership.isCluster`), the transport started with its
  peers added (2f), the environment's permission `envUpd γ ecfg` (for the apply thread: lease
  expiry, alarms, publication, compaction, K5), and the member's `memberDisk` contents, moved into
  the running server's invariant (the WAL's records, the snapshot dbs, the backend file).
* `isServer s γ`: the request path's invariant (2c) and the fields `start` sets (the wait
  registry, the apply-wait list, the stop channels, the read loop's handle, the leader notifier).
* `srvRunning s γ id ds`: the right to send on `s.stop`, with the escrow of `s.done`'s closing:
  `run`'s stop deposits `memberDisk γ id ds` there (2d's `run`).

## Slots (the slot convention, `specs-ref/notes/spec-first-plan.md`, "The slot convention")

`NewServer`'s premises name each subsystem once, by a sealed predicate its owner states. Mine:
`V3compactor.bootCfg` (`api/v3compactor/Api.lean`). The others' owners have no API module yet; the
**provisional slots** below stand for them (as raft's `Api.lean` stands for raftpb's), each
requested in the owner's `req/` file, to be replaced by the owner's at integration:
`raftNodeBootCfg` (2d), `v3rpcBootCfg` (2a: K8's two bounds), `mvccBootCfg` (3e),
`backendBootRes` (4a), `leaseBootRes` (3c), `authBootRes` (3d), `rafthttpBootCfg` (2f). No WAL or
snapshotter slot: neither has a condition on the configuration (no crash in scope: `UnsafeNoFsync`
loses nothing a stop and restart see).

## Internal vocabulary (the package's own proofs: `bootstrap`, `start`, the closers)

`bootOk b γ id cfg` (what `bootstrap` returns), `bootRaftOk br γ id cfg`, `bootBackendAt b be`,
`srvPublish s`, `srvPurge s`, `stoppingCh ch`: see each declaration.

## Laws

`srvMember_persistent`, `srvMember_agree`, `isServer_persistent`, `memberDisk_timeless`,
`memberDisk_excl`, `dataDirFresh_timeless`, `dataDirFresh_excl`, `memberBoot_timeless`,
`memberJoin_excl`, `memberUrls_excl`, `cluster_alloc`, `memberUrls_take`, `memberStart_new`,
`memberStart_join`, `memberStart_restart`, `stoppingCh_persistent`.

## Requirement snippets

`examples/specreq/etcdserverboot/`: `boot.go` (a new cluster of one and of three members, started
and served; a joining member; a member stopped and restarted on its directory, the read after the
restart sees the writes made while it was down), `stop.go` (stop paths: a never-started build, a
stop after a server error), `config.go` (the configurations the starters build, K8's scope).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.State
public import Spec.go_etcd_io.etcd.server.v3.config.Api
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Api
public import Spec.go_etcd_io.raft.v3.Model
public import Spec.PkgInit.go_etcd_io.etcd.server.v3.etcdserver

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext]

/-! ## Files and starts -/

/-- **Nothing of etcd's is in the directories `ds`** (exclusive, timeless): no WAL directory, no
backend file, no snapshot file. From program start (see the header). -/
opaque dataDirFresh (ds : Config.Dirs) : IProp GF := iprop(True)

/-- **Member `m` of the new cluster `γ` of initial members `ms` may start once** (exclusive). -/
opaque memberBoot (γ : Cluster) (ms : List Member) (m : Member) : IProp GF := iprop(True)

/-- **The peer-URL sets taken so far** (the initial members' and every `memberUrls_take`'s;
exclusive). -/
opaque memberUrls (γ : Cluster) (U : List (List GoString)) : IProp GF := iprop(True)

/-- **A member with the peer URLs `urls` may join `γ` once, from a fresh directory**
(exclusive). -/
opaque memberJoin (γ : Cluster) (urls : List GoString) : IProp GF := iprop(True)

/-- **The directories `ds` hold the durable state of member `id` of `γ`, stopped** (exclusive,
timeless; client-owned). -/
opaque memberDisk (γ : Cluster) (id : Nat) (ds : Config.Dirs) : IProp GF := iprop(True)

/-- **The right to start a member of `γ` with configuration `cfg`** (whose heap parts are `c`):
exclusive; introduced by `memberStart_new`, `memberStart_join`, `memberStart_restart`. -/
opaque memberStart (γ : Cluster) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (c : Config.Model) : IProp GF := iprop(True)

/-! ## The server object -/

/-- **`s` is the server object of member `id` of `γ`** (persistent): built by `NewServer`. -/
opaque srvMember (s : Loc) (γ : Cluster) (id : Nat) : IProp GF := iprop(True)

/-- **`s` is built from `cfg` and not started** (exclusive). -/
opaque srvBuilt (s : Loc) (γ : Cluster) (id : Nat)
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : IProp GF := iprop(True)

/-- **`s` serves `γ`** (persistent): started; the request path's handle (2c's specs take it). -/
opaque isServer (s : Loc) (γ : Cluster) : IProp GF := iprop(True)

/-- **The right to stop `s`, member `id` of `γ` whose files are in `ds`** (exclusive). -/
opaque srvRunning (s : Loc) (γ : Cluster) (id : Nat) (ds : Config.Dirs) : IProp GF := iprop(True)

/-! ## Internal (the package's proofs) -/

/-- `bootstrap`'s result `b` for member `id` of `γ` and configuration `cfg` (exclusive): one
sealed conjunct per subsystem (`Wal`'s opened WAL and its records, `Snap`'s snapshotter and dbs,
the backend open with its hooks and consistent index, the membership view with the remote members
to add, the raft record `bootRaftOk`, the peers' round tripper). -/
opaque bootOk (b : Loc) (γ : Cluster) (id : Nat)
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : IProp GF := iprop(True)

/-- `bootstrap`'s raft record `br` (exclusive): its configuration, peers and `MemoryStorage`, for
`StartNode` (a new member: peers non-empty) or `RestartNode` (no peers), with what raft's start
spec takes of the storage and the durable state. -/
opaque bootRaftOk (br : Loc) (γ : Cluster) (id : Nat)
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : IProp GF := iprop(True)

/-- The record `b` (a `*bootstrappedServer`, `*bootstrappedStorage` or `*bootstrappedBackend`)
reaches the backend `be` through read-only fields (persistent). -/
opaque bootBackendAt (b : Loc) (be : GoInterface) : IProp GF := iprop(True)

/-- The right to close `s.readych` once (`publishV3`). -/
opaque srvPublish (s : Loc) : IProp GF := iprop(True)

/-- The WAL purge's handle (persistent): the invariant that holds `Wal.walPurgeRight` while no
purge runs. -/
opaque srvPurge (s : Loc) : IProp GF := iprop(True)

/-- `ch` is a server's stopping channel (persistent): closed at most once, by the stop; anyone
may receive from it. -/
opaque stoppingCh (ch : GoChan) : IProp GF := iprop(True)

/-! ## Provisional slots of other batches (see the header) -/

/-- **Provisional slot (2d, the raft node):** the raft node's configuration: a positive heartbeat
(`time.Duration(TickMs) * time.Millisecond`, wrapping: `time.NewTicker` panics at `≤ 0`) and a raft
`Config` that validates (`ElectionTicks > 1`: `StartNode`/`RestartNode` panic on an invalid one). -/
opaque raftNodeBootCfg (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : Prop

/-- **Provisional slot (2a, the gRPC handlers):** K8's scope restrictions: `MaxTxnOps ≤ 4999`
(`issues/etcd-txn-nested-depth-apply-panic.md`), `MaxRequestBytes` below the bound of
`issues/etcd-txn-keysonly-reply-alloc-panic.md`. -/
opaque v3rpcBootCfg (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : Prop

/-- **Provisional slot (3e, mvcc):** the store's configuration (`CompactionBatchLimit`:
`nonissues/etcd-compaction-negative-batch-limit.md`). -/
opaque mvccBootCfg (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : Prop

/-- **Provisional slot (2f, rafthttp):** the transport's configuration (its peer URLs, the
cluster's directory within the transport's bounds). -/
opaque rafthttpBootCfg (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : Prop

/-- **Provisional slot (4a, the backend):** the backend's configuration (`QuotaBackendBytes` a size
bbolt can map: `nonissues/etcd-quota-backend-bytes-mmap-panic.md`) and its program-start facts
(`ETCD_VERIFY` unset for the run: the axiom sweep's batch 1). Persistent. -/
opaque backendBootRes (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : IProp GF :=
  iprop(True)

/-- **Provisional slot (3c, the lessor):** the lessor's configuration against the environment's
lease mode (with `ecfg.leaseExpiry = false`, the deployment premise that no lease expires during
the run: the lessor's own statement), and the checkpointer's effects. Persistent. -/
opaque leaseBootRes (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (ecfg : EnvCfg) :
    IProp GF := iprop(True)

/-- **Provisional slot (3d, auth):** the token provider's configuration (`AuthToken`, `TokenTTL`,
`BcryptCost`). Persistent. -/
opaque authBootRes (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : IProp GF := iprop(True)

/-! ## Laws -/

def srvMember_persistent.spec : Prop := ∀ s γ id, Persistent (srvMember (GF := GF) s γ id)

def srvMember_agree.spec : Prop := ∀ s γ γ' id id',
  srvMember (GF := GF) s γ id ∗ srvMember s γ' id' ⊢ ⌜γ = γ' ∧ id = id'⌝

def isServer_persistent.spec : Prop := ∀ s γ, Persistent (isServer (GF := GF) s γ)

def stoppingCh_persistent.spec : Prop := ∀ ch, Persistent (stoppingCh (GF := GF) ch)

def memberDisk_timeless.spec : Prop := ∀ γ id ds, Timeless (memberDisk (GF := GF) γ id ds)

/-- One durable state per member id (raft's `raftState` is exclusive per id). -/
def memberDisk_excl.spec : Prop := ∀ γ id ds ds',
  memberDisk (GF := GF) γ id ds ∗ memberDisk γ id ds' ⊢ iprop(False)

def dataDirFresh_timeless.spec : Prop := ∀ ds, Timeless (dataDirFresh (GF := GF) ds)

def dataDirFresh_excl.spec : Prop := ∀ ds,
  dataDirFresh (GF := GF) ds ∗ dataDirFresh ds ⊢ iprop(False)

def memberBoot_timeless.spec : Prop := ∀ γ ms m, Timeless (memberBoot (GF := GF) γ ms m)

def memberJoin_excl.spec : Prop := ∀ γ urls urls', urls.Perm urls' →
  memberJoin (GF := GF) γ urls ∗ memberJoin γ urls' ⊢ iprop(False)

def memberUrls_excl.spec : Prop := ∀ γ U U',
  memberUrls (GF := GF) γ U ∗ memberUrls γ U' ⊢ iprop(False)

/-- **K1: a new cluster** of the members `ms` (each with the id `bootstrap` computes:
`Membership.initialMembers`): the state, one start token per member, their URL sets taken. -/
def cluster_alloc.spec : Prop := ∀ (ms : List Member) (E : CoPset),
  ⊢ |={E}=> ∃ γ : Cluster, etcdState (GF := GF) γ (State.init ms) ∗
      memberUrls γ (ms.map (·.peerURLs)) ∗ [∗list] m ∈ ms, memberBoot γ ms m

/-- **A peer-URL set for a member to join** (before or after its `MemberAdd`): taken once. -/
def memberUrls_take.spec : Prop := ∀ (γ : Cluster) (U : List (List GoString))
    (urls : List GoString),
  (∀ u ∈ U, ¬ u.Perm urls) →
  memberUrls (GF := GF) γ U ⊢ |==> memberUrls γ (urls :: U) ∗ memberJoin γ urls

/-- **Start a member of a new cluster**: its boot token and a fresh directory, under a
configuration of a new cluster whose initial members are the allocated ones (`NewCluster`, the
initial-cluster map and token computing `ms`, the member's name). -/
def memberStart_new.spec : Prop :=
  ∀ (γ : Cluster) (ms : List Member) (m : Member)
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (c : Config.Model),
  cfg.NewCluster' = true → m ∈ ms → m.name = cfg.Name' →
  (Membership.initialMembers cfg.InitialClusterToken' c.initialCluster).Perm ms →
  memberBoot (GF := GF) γ ms m ∗ dataDirFresh (Config.dirsOf cfg) ⊢ memberStart γ cfg c

/-- **Join as the member added with the configuration's peer URLs** (listed under the
configuration's own name in the initial-cluster map): its join token and a fresh directory. -/
def memberStart_join.spec : Prop :=
  ∀ (γ : Cluster) (urls : List GoString)
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (c : Config.Model),
  cfg.NewCluster' = false → urls.Perm c.peerURLs →
  (∃ u, c.initialURLs cfg.Name' = some u ∧ u.Perm c.peerURLs) →
  memberJoin (GF := GF) γ urls ∗ dataDirFresh (Config.dirsOf cfg) ⊢ memberStart γ cfg c

/-- **Restart a stopped member** on its directories (any configuration but
`--force-new-cluster`, a disaster-recovery mode outside the protocol: R1's `RestartNode`
Margin). -/
def memberStart_restart.spec : Prop :=
  ∀ (γ : Cluster) (id : Nat) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (c : Config.Model),
  cfg.ForceNewCluster' = false →
  memberDisk (GF := GF) γ id (Config.dirsOf cfg) ⊢ memberStart γ cfg c

end vocab

end EtcdServer
end EtcdGrove
end Perennial
