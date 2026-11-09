/-
# A member's lifecycle: allocation, start, serving, stop, restart (batch 2e)

The vocabulary of `NewServer`, `Start`, `Stop`/`HardStop` and the cluster contract's start-up
part (`notes/specs-only/top.md`, K1-K3, K6; `req/go_etcd_io_etcd_server_v3_etcdserver.md`,
"from W0"). Namespace `EtcdServer`, shared with the request path (2c) and the apply thread (2d),
whose `Api.lean` modules import this one: `isServer`/`srvGate` below are what their specs take;
2d's `ApiApply.lean` bridges them to its `Names` (`isServer_names`, `srvMember_node`,
`srvRunTok_intro`, `srvStopped_disk`).

## The shape, in words

**A cluster** is W0's `Cluster` (`api/v3/State.lean`). The program allocates its state with the
members it will start (`cluster_alloc`, K1). It hands in **the peer addresses** of every initial
member (`Http.addrFree a` for each host of their peer URLs: 2f's closed world, so two allocations
cannot share an address: round 1, provability F3) and **the members' shared apply configuration**
(`ApplyCfg`, 2d's `MemberCfg`: every member's configuration must have it, `applyCfgIs cfg mc`). It gets
`etcdState γ (State.init ms)` in full, one `memberBoot γ ms m` per initial member, the cluster's
raft network `srvNet γ ν` (2f's `Net`) and, for each reserved host, the persistent
`Http.protoAt a (Rafthttp.raftProto ν)` with which the program serves the member's raft handler.

**A member's files** are keyed by its directories (`Config.Dirs`). At program start a directory
is `dataDirFresh ds` (the adequacy theorem's per-directory token: the paths pairwise distinct for
the whole run, canonical, no other string naming one of them: the axiom sweep's B3-1; to be listed
in W0's adequacy statement). A stopped member's directories are `memberDisk γ id ds`: its durable
state, client-owned; nothing else is needed to start the member again on it.

**Peer-URL sets are single-use** (round 1, provability F4). `urls_reserve` turns the addresses of a
new URL set into `urlsRight γ urls` and `memberJoin γ urls`. Every request that gives a member a
URL set takes its `urlsRight` (`EtcdServer.AddMember`, `UpdateMember`); the initial members' are
spent by `cluster_alloc`. So a URL set names at most one member over the cluster's life, and a
joiner holding `memberJoin γ urls` runs as the member added under `urls` (`bootstrap` assigns the
id the cluster has for those URLs, `ValidateClusterAndAssignIDs`): no `MemberUpdate` can move
another member onto them. Cost: a removed member's URL set cannot be used again (a scope
restriction, `batch-2e.md` Q1).

**Starting a member** (`NewServer`, K2) takes `memberStart γ cfg c oid` (`oid`: the member id when
it is known before the start), introduced in three ways:
* a member of a new cluster (`memberStart_new`, `oid = some m.id`): its `memberBoot` and a fresh
  directory, the configuration a new cluster's whose initial members are the allocated ones;
* a joiner (`memberStart_join`, `oid = none`): `memberJoin γ urls` and a fresh directory, the
  configuration's peer URLs `urls`, `NewCluster` false;
* a stopped member (`memberStart_restart`, `oid = some id`): its `memberDisk`.
It also takes `envUpd γ ecfg` (W0's), `clusterApplyCfg γ mc` with `applyCfgIs cfg mc`, the
configuration's scope premises (one sealed slot per subsystem, below), the logger, the feature gate,
the configuration's heap parts and the disk premise. It returns a member id `id`, non-zero and below
`2 ^ 64`, `oid`'s if given, with `srvMember s γ id` (persistent) and `srvBuilt s γ id cfg`.

**Starting it** (`Start`) turns `srvBuilt` into `isServer s γ` (persistent: the handle 2a's
`v3rpc.Server` and 2c's request path take), `srvGate s 1` (fractional: **every request-path call
holds a share for its duration**) and `srvRunning s γ id ds` (exclusive). A `threadTok` goes with
the goroutines `Start` attaches.

**Stopping it** (`HardStop`, `Stop`) takes `srvRunning` and **the whole gate** `srvGate s 1`: no
request is in flight (round 1, completeness F2: `Cleanup` closes the backend under in-flight readers
otherwise, `issues/etcd-read-after-backend-close-panic.md`; a program drains its gRPC server first,
or serves none: `restart3`). It gives back `memberDisk γ id ds`. The alternative, a gate in the Go
code (reads take it shared, `Cleanup` exclusively after the server is marked stopped, later reads
fail with `ErrStopped`), would let `isServer` serve a stopped server: recorded as the fork fix the
user may choose (`batch-2e.md` Q7).

## Intended realization

* `Cluster` holds raft's cluster names (`Raft.Cluster`, `dup = false`: 2d), the raft network `ν`
  (2f's `Net`, its `img`/`dbIn` the server's: a database image of the committed state through `i`;
  a saved file of index `i` in the member's snapshot directory), the URL-set authority, the shared
  `ApplyCfg`; `etcdState` is 2c/2d's.
* `memberBoot γ ms m`: raft's `raftState γ.raft m.id Durable.init ∗ nodeVacant γ.raft m.id` (raft's
  `cluster_alloc` at `ms`'s ids, the contexts `bootstrap` computes), the boot log's `confDecided`
  facts, `peerAddr ν a` of every member's hosts. When the ids of `ms` are not distinct or include
  `0`, `bootstrap` fails for every member (`NewClusterFromURLsMap`): a classical case split.
* `urlsRight γ urls` / `memberJoin γ urls`: two halves of the URL set's entry in the cluster's
  invariant (which sees every committed `MemberAdd`/`MemberUpdate`): while the join right is pending,
  the invariant keeps `raftState γ.raft id Durable.init ∗ nodeVacant γ.raft id` of the id added
  under `urls` (raft's `freshIds_take`: etcd commits an add only of an id it never saw,
  `ErrIDRemoved`/`ErrIDExists`), and `peerAddr ν a` of its hosts.
* `memberDisk γ id ds` (the R2d'a lesson: every binder tied to the files): `∃ R img D ci,
  Wal.walRecs (walDirOf ds) R ∗ Snap.beFile (backendPathOf ds.dataDir) (some img) ∗ raftState
  γ.raft id D ∗ nodeVacant γ.raft id ∗ ⌜walHolds R D⌝ ∗ beHolds γ img ci ∗ ⌜R.readable⌝ ∗ snapDel
  (snapDirOf ds.dataDir) ∗ snapHas … ∗ peerAddr ν a …`: `walHolds R D`, the restart view of `R`
  (`R.newest`, `R.hs`, `R.entsAfter`) is `D`'s (raft's `StorageHolds` of the `MemoryStorage`
  `bootstrap` rebuilds); `beHolds`, the backend image is the committed log's state through its
  consistent index `ci` with its configuration (`confAt γ.raft ci m`), **`ci` not bounded by the
  WAL's commit** (R1's restart at any committed `a`). **The snapshot directory is not moved into
  `memberDisk`** (round 1, provability F5): `Snap.snapDbs` lives for good in a per-directory
  invariant (allocated from `dataDirFresh`), whose files of index `i` hold images certified for `i`
  (`ν.img`); any raft handler, of any incarnation, may add to it through `SaveDBFrom` (`saveAt` keeps
  an existing file), also after `HardStop` (`http.Serve` has no drain, and a handler outlives its
  listener's close). Only removals are exclusive: `memberDisk` (and the running server) hold the
  deletion right `snapDel` (`ReleaseSnapDBs`, `OpenSnapshotBackend`'s rename), with which the
  restart knows the file at the WAL's newest snapshot index is there when `ci` is below it.
* `memberStart γ cfg c oid`: the disjunction of the three introductions' left sides at their
  conditions.
* `srvMember s γ id`: read-only fields (`memberID`, `r.transport`: 2f's `isTransport` of `ν` and
  `id`, `cluster`, `lgMu`/`lg`, `Cfg`), 2d's `srvNode` (`srvMember_node`), `⌜0 < id < 2 ^ 64⌝`.
* `srvBuilt s γ id cfg`: one conjunct per subsystem (the slot convention): the raft node and its
  storage (2d), the backend, its hooks and the consistent index (4a, 2d), the lessor (3c), the KV
  store (3e), the auth store (3d), the alarm store, the compactor, the membership view, the
  transport (2f), `envUpd γ ecfg`, and the member's files' contents moved into the running server's
  invariant (the WAL's records, the backend file, the deletion right): the node's running token for
  `id`, hence `srvBuilt_excl`.
* `isServer s γ`: the request path's invariant (2c) and the fields `start` sets; `srvGate s q`: a
  fractional token of the store's and the backend's readers (3e's, 4a's reader tokens), which the
  stop's census rebuilds into the backend's whole open token for `Cleanup`.
* `srvRunning s γ id ds`: the right to send on `s.stop`, with the escrow of `s.done`'s closing:
  `run`'s stop deposits 2d's `srvStopped`, which with `Cleanup`'s `srvClosed` is `memberDisk`
  (2d's `srvStopped_disk`).

## Crashes (round 1, completeness F8: attempted; a blocker found)

The general version keeps `memberDisk` client-owned throughout the run: the server holds only an
access (a persistent update over it that the WAL's `Save` fires), and a crash leaves `memberDisk`
with the records `Wal.Recs.crashed`/`crashedMid` allow (stated in `wal/Api.lean`, true of the WAL's
code). **Blocker: raft's durable node API (R1).** A crash during a `Save` leaves a prefix of the
batch's entry records (written, not fsynced) and the old state record: a log that is neither raft's
durable state `D` before the batch nor after it (`Durable.next`), possibly truncated at the batch's
first index with only some new entries, and with entries of a term above the stored term. R1's
`raftState γ id D` moves only at a `Ready`'s update, and `StorageHolds D σ` requires the stored log to
be `D`'s, so `RestartNode.spec` cannot be applied to such a directory. Lifting it needs a crash
transition of R1's durable state (`raftState γ id D ⊢ raftState γ id D'` for `D'` a partly applied
batch, with raft's invariants shown to admit it), requested in `req/go_etcd_io_raft_v3.md`, "from 2e,
round 1". Until then the specs restart after a graceful stop only (`HardStop`/`Stop`), and the
`memberDisk` they give back is the one a crash rule will also give.

## Slots (the slot convention, `specs-ref/notes/spec-first-plan.md`, "The slot convention")

`NewServer`'s premises name each subsystem once. Mine: `V3compactor.bootCfg`. The others are
**provisional** (their owners have no API module yet), each with the introduction law its owner
must keep (round 1, completeness F1), requested in the owner's `req/` file: `raftNodeBootCfg` (2d),
`v3rpcBootCfg` (2a), `mvccBootCfg` (3e), `backendBootRes` (4a, from the program-start
`backendEnvOk`), `leaseBootRes` (3c), `authBootRes` (3d). 2f's former `rafthttpBootCfg` is gone: the
transport's needs (its peer addresses) come with `memberStart` and `cluster_alloc`. No WAL or
snapshotter slot (restarts after a stop: `UnsafeNoFsync` loses nothing a stop and restart see; the
crash rule will need `UnsafeNoFsync = false`).

## Laws

`srvMember_persistent`, `srvMember_agree`, `srvMember_id`, `isServer_persistent`,
`srvGate_fractional`, `srvBuilt_excl`, `srvRunning_excl`, `srvBuilt_running_excl`,
`stoppingCh_persistent`, `doneCh_persistent`, `readyCh_persistent`, `srvNet_persistent`,
`srvNet_agree`, `clusterApplyCfg_persistent`, `clusterApplyCfg_agree`, `memberDisk_timeless`,
`memberDisk_excl`, `dataDirFresh_timeless`, `dataDirFresh_excl`, `memberBoot_timeless`,
`memberJoin_excl`, `urlsRight_excl`, `cluster_alloc`, `urls_reserve`, `memberStart_new`,
`memberStart_join`, `memberStart_restart`, `srvBuilt_closers`, and the slots' introductions
`raftNodeBootCfg_intro`, `v3rpcBootCfg_intro`, `mvccBootCfg_intro`, `backendBootRes_intro`,
`leaseBootRes_intro`, `authBootRes_intro`.

## Requirement snippets

`examples/specreq/etcdserverboot/boot.go` (a new cluster of one and of three members; a member
stopped and restarted on its directory; a join; partitions; the stop after a server error; the
cleanup before start; a request racing the stop), `lock.go` (the Lock service over the in-process
client), and the Go tests of the trusted models: `storage.go`, `snap.go`, `members.go`.
-/
module

public import Spec.go_etcd_io.etcd.api.v3.State
public import Spec.go_etcd_io.etcd.server.v3.config.Api
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Api
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Api
public import Spec.go_etcd_io.raft.v3.Model
public import Spec.PkgInit.go_etcd_io.etcd.server.v3.etcdserver

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel

/-- **The members' shared apply configuration** (provisional: 2d's/3a's `MemberCfg`: the leases'
minimum TTL, ...): the part of a member's configuration the apply's model depends on. -/
opaque ApplyCfg : Type := Unit

/-- `cfg`'s apply configuration is `mc` (provisional, 2d's/3a's: a function of the configuration's
fields, e.g. the lease checkpoint settings and the election timing that fix the minimum TTL). -/
opaque applyCfgIs [GooseExts] [GoGlobalContext]
  (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (mc : ApplyCfg) : Prop

/-- The member list a membership answer carries (the members after the change). -/
def respMembers : Resp → Option (List Member)
  | .ok (.memberAdd _ l) => some l
  | .ok (.memberRemove l) => some l
  | .ok (.memberUpdate l) => some l
  | .ok (.memberPromote l) => some l
  | _ => none

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics] [rsem : go_etcd_io.raft.v3.Assumptions]

/-! ## The cluster, its addresses, its files -/

/-- **The raft network of cluster `γ` is `ν`** (persistent). -/
opaque srvNet (γ : Cluster) (ν : Rafthttp.Net GF) : IProp GF := iprop(True)

/-- **The members of `γ` share the apply configuration `mc`** (persistent). -/
opaque clusterApplyCfg (γ : Cluster) (mc : ApplyCfg) : IProp GF := iprop(True)

/-- **Nothing of etcd's is in the directories `ds`** (exclusive, timeless). -/
opaque dataDirFresh (ds : Config.Dirs) : IProp GF := iprop(True)

/-- **Member `m` of the new cluster `γ` of initial members `ms` may start once** (exclusive). -/
opaque memberBoot (γ : Cluster) (ms : List Member) (m : Member) : IProp GF := iprop(True)

/-- **The right to give a member of `γ` the peer URLs `urls`, once** (exclusive): taken by
`AddMember`/`UpdateMember`. -/
opaque urlsRight (γ : Cluster) (urls : List GoString) : IProp GF := iprop(True)

/-- **The member added with the peer URLs `urls` may join `γ` once, from a fresh directory**
(exclusive). -/
opaque memberJoin (γ : Cluster) (urls : List GoString) : IProp GF := iprop(True)

/-- **The directories `ds` hold the durable state of member `id` of `γ`, stopped** (exclusive,
timeless; client-owned). -/
opaque memberDisk (γ : Cluster) (id : Nat) (ds : Config.Dirs) : IProp GF := iprop(True)

/-- **The right to start a member of `γ` with configuration `cfg`** (heap parts `c`), member
`oid` when known: exclusive; introduced by `memberStart_new`, `_join`, `_restart`. -/
opaque memberStart (γ : Cluster) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (c : Config.Model) (oid : Option Nat) : IProp GF := iprop(True)

/-! ## The server object -/

/-- **`s` is the server object of member `id` of `γ`** (persistent): built by `NewServer`. -/
opaque srvMember (s : Loc) (γ : Cluster) (id : Nat) : IProp GF := iprop(True)

/-- **`s` is built from `cfg` and not started** (exclusive). -/
opaque srvBuilt (s : Loc) (γ : Cluster) (id : Nat)
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : IProp GF := iprop(True)

/-- **`s` serves `γ`** (persistent): started; the request path's handle. -/
opaque isServer (s : Loc) (γ : Cluster) : IProp GF := iprop(True)

/-- **A share `q` of the right to call `s`'s request path** (fractional): every request-path call
holds a share for its duration; the stop takes it whole (no request in flight). -/
opaque srvGate (s : Loc) (q : Qp) : IProp GF := iprop(True)

/-- **The right to stop `s`, member `id` of `γ` whose files are in `ds`** (exclusive). -/
opaque srvRunning (s : Loc) (γ : Cluster) (id : Nat) (ds : Config.Dirs) : IProp GF := iprop(True)

/-- `ch` is a server's stopping channel (persistent): closed at most once, by the stop. -/
opaque stoppingCh (ch : Loc) : IProp GF := iprop(True)

/-- `ch` is `s.done` (persistent): closed when `run`'s stop is over; a receive gives nothing (the
deposit stays for `srvRunning`). -/
opaque doneCh (s : Loc) (ch : Loc) : IProp GF := iprop(True)

/-- `ch` is `s.readych` (persistent): closed once the member published itself; a receive gives
nothing. -/
opaque readyCh (s : Loc) (ch : Loc) : IProp GF := iprop(True)

/-! ## Internal (the package's proofs) -/

/-- `bootstrap`'s result `b` for member `id` of `γ` and configuration `cfg` (exclusive). -/
opaque bootOk (b : Loc) (γ : Cluster) (id : Nat)
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : IProp GF := iprop(True)

/-- `bootstrap`'s raft record `br` (exclusive). -/
opaque bootRaftOk (br : Loc) (γ : Cluster) (id : Nat)
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : IProp GF := iprop(True)

/-- The record `b` reaches the backend `be` through read-only fields (persistent). -/
opaque bootBackendAt (b : Loc) (be : GoInterface) : IProp GF := iprop(True)

/-- The right to close `s.readych` once (`publishV3`). -/
opaque srvPublish (s : Loc) : IProp GF := iprop(True)

/-- The WAL purge's handle (persistent): the invariant holding `Wal.walPurgeRight` while no purge
runs. -/
opaque srvPurge (s : Loc) : IProp GF := iprop(True)

/-- `cc` is `s`'s corruption checker over the hash storage `hs` (persistent). -/
opaque isCorruptionChecker (cc : Loc) (s : Loc) (hs : GoInterface) : IProp GF := iprop(True)

/-- What `Cleanup` closes (exclusive): the lessor's stop right, the KV store's closer with its
readers given back, the auth store's closer, the backend's whole open token, the compactor's handle. -/
opaque srvClosers (s : Loc) (ds : Config.Dirs) : IProp GF := iprop(True)

/-- What `Cleanup` gives back (exclusive): the backend's file at rest. -/
opaque srvClosed (ds : Config.Dirs) : IProp GF := iprop(True)

/-! ## Provisional names of other batches' vocabulary (replaced at integration) -/

/-- **Provisional (2d):** `rn` is the raft node `newRaftNode` built for member `id` of `γ` over the
storage `st`. Exclusive. -/
opaque raftNodeBuilt (rn : Loc) (γ : Cluster) (id : Nat) (st : Loc) : IProp GF := iprop(True)

/-- **Provisional (2f):** `tp` is a `rafthttp.Transporter` (the `Transporter` bundle of a
transport's interface value: `ActiveSince`/`ActivePeers` each taking and giving back a
`threadTok`). Persistent. -/
opaque transporterOk (tp : GoInterface) : IProp GF := iprop(True)

/-- **Provisional (3h):** `r` is `nil` (`b = false`) or a readable `*InternalRaftRequest` whose
`LeaseRevoke` is set exactly when `b`. Persistent. -/
opaque irrIsRevoke (r : Loc) (b : Bool) : IProp GF := iprop(True)

/-- **Provisional (W0's metrics boundary):** `gv` is a usable `*prometheus.GaugeVec`. -/
opaque gaugeVecOk (gv : Loc) : IProp GF := iprop(True)

/-- **Provisional (4a; a program-start fact W0's adequacy lists):** `ETCD_VERIFY` is unset for
the whole run (the backend's verification hooks panic otherwise: the axiom sweep's batch 1).
Persistent. -/
opaque backendEnvOk : IProp GF := iprop(True)

/-! ## Provisional slots (see the header) -/

/-- **Provisional slot (2d):** the raft node's configuration. -/
opaque raftNodeBootCfg (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : Prop

/-- **Provisional slot (2a):** K8's scope restrictions. -/
opaque v3rpcBootCfg (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : Prop

/-- **Provisional slot (3e):** the store's configuration. -/
opaque mvccBootCfg (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : Prop

/-- **Provisional slot (4a):** the backend's configuration and program-start facts. -/
opaque backendBootRes (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : IProp GF :=
  iprop(True)

/-- **Provisional slot (3c):** the lessor's configuration against the environment's lease mode. -/
opaque leaseBootRes (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (ecfg : EnvCfg) :
    IProp GF := iprop(True)

/-- **Provisional slot (3d):** the token provider's configuration. -/
opaque authBootRes (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : IProp GF := iprop(True)

/-! ## The slots' introductions (what their owners must keep) -/

/-- The raft node: a validating raft configuration (`ElectionTicks > 1`; `HeartbeatTick` is `1`)
and a non-negative heartbeat (a zero one ticks never: liveness only; 2d's item 10). -/
def raftNodeBootCfg_intro.spec : Prop := ∀ cfg : go_etcd_io.etcd.server.v3.config.ServerConfig,
  1 < sint.Z cfg.ElectionTicks' → 0 ≤ sint.Z (cfg.TickMs' * W64 1000000) → raftNodeBootCfg cfg

/-- K8: at most 4999 operations per transaction, a request limit of at most 10 MiB (2a refines). -/
def v3rpcBootCfg_intro.spec : Prop := ∀ cfg : go_etcd_io.etcd.server.v3.config.ServerConfig,
  sint.Z cfg.MaxTxnOps' ≤ 4999 → uint.Z cfg.MaxRequestBytes' ≤ 10 * 1024 * 1024 → v3rpcBootCfg cfg

/-- The store: a non-negative compaction batch limit. -/
def mvccBootCfg_intro.spec : Prop := ∀ cfg : go_etcd_io.etcd.server.v3.config.ServerConfig,
  0 ≤ sint.Z cfg.CompactionBatchLimit' → mvccBootCfg cfg

/-- The backend: `ETCD_VERIFY` unset, and the default quota or one of at most 8 GiB (bbolt maps
`quota + quota / 10`). -/
def backendBootRes_intro.spec : Prop := ∀ cfg : go_etcd_io.etcd.server.v3.config.ServerConfig,
  sint.Z cfg.QuotaBackendBytes' ≤ 8 * 1024 * 1024 * 1024 →
  backendEnvOk (GF := GF) ⊢ backendBootRes cfg

/-- The lessor: leases may expire in the environment (the mode without expiry needs 3c's
deployment premise: `batch-2e.md` Q6). -/
def leaseBootRes_intro.spec : Prop := ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (ecfg : EnvCfg), ecfg.leaseExpiry = true → ⊢ leaseBootRes (GF := GF) cfg ecfg

/-- Auth: the simple token provider (etcd's default). -/
def authBootRes_intro.spec : Prop := ∀ cfg : go_etcd_io.etcd.server.v3.config.ServerConfig,
  cfg.AuthToken' = go!"simple" → ⊢ authBootRes (GF := GF) cfg

/-! ## Laws -/

def srvMember_persistent.spec : Prop := ∀ s γ id, Persistent (srvMember (GF := GF) s γ id)

def srvMember_agree.spec : Prop := ∀ s γ γ' id id',
  srvMember (GF := GF) s γ id ∗ srvMember s γ' id' ⊢ ⌜γ = γ' ∧ id = id'⌝

/-- A member id is a non-zero `uint64` (`NewClusterFromURLsMap` refuses `0`; the WAL's metadata). -/
def srvMember_id.spec : Prop := ∀ s γ id,
  srvMember (GF := GF) s γ id ⊢ ⌜0 < id ∧ id < 2 ^ 64⌝

def isServer_persistent.spec : Prop := ∀ s γ, Persistent (isServer (GF := GF) s γ)

def srvGate_fractional.spec : Prop := ∀ s (q₁ q₂ : Qp),
  srvGate (GF := GF) s (q₁ + q₂) ⊣⊢ srvGate s q₁ ∗ srvGate s q₂

/-- One running node per member id: two built servers of one member cannot coexist. -/
def srvBuilt_excl.spec : Prop := ∀ s s' γ id cfg cfg',
  srvBuilt (GF := GF) s γ id cfg ∗ srvBuilt s' γ id cfg' ⊢ iprop(False)

def srvRunning_excl.spec : Prop := ∀ s s' γ id ds ds',
  srvRunning (GF := GF) s γ id ds ∗ srvRunning s' γ id ds' ⊢ iprop(False)

def srvBuilt_running_excl.spec : Prop := ∀ s s' γ id cfg ds,
  srvBuilt (GF := GF) s γ id cfg ∗ srvRunning s' γ id ds ⊢ iprop(False)

def stoppingCh_persistent.spec : Prop := ∀ ch, Persistent (stoppingCh (GF := GF) ch)
def doneCh_persistent.spec : Prop := ∀ s ch, Persistent (doneCh (GF := GF) s ch)
def readyCh_persistent.spec : Prop := ∀ s ch, Persistent (readyCh (GF := GF) s ch)

def srvNet_persistent.spec : Prop := ∀ γ ν, Persistent (srvNet (GF := GF) γ ν)
def srvNet_agree.spec : Prop := ∀ γ ν ν', srvNet (GF := GF) γ ν ∗ srvNet γ ν' ⊢ ⌜ν = ν'⌝

def clusterApplyCfg_persistent.spec : Prop := ∀ γ mc, Persistent (clusterApplyCfg (GF := GF) γ mc)
def clusterApplyCfg_agree.spec : Prop := ∀ γ mc mc',
  clusterApplyCfg (GF := GF) γ mc ∗ clusterApplyCfg γ mc' ⊢ ⌜mc = mc'⌝

def memberDisk_timeless.spec : Prop := ∀ γ id ds, Timeless (memberDisk (GF := GF) γ id ds)

/-- One durable state per member id. -/
def memberDisk_excl.spec : Prop := ∀ γ id ds ds',
  memberDisk (GF := GF) γ id ds ∗ memberDisk γ id ds' ⊢ iprop(False)

def dataDirFresh_timeless.spec : Prop := ∀ ds, Timeless (dataDirFresh (GF := GF) ds)

def dataDirFresh_excl.spec : Prop := ∀ ds,
  dataDirFresh (GF := GF) ds ∗ dataDirFresh ds ⊢ iprop(False)

def memberBoot_timeless.spec : Prop := ∀ γ ms m, Timeless (memberBoot (GF := GF) γ ms m)

def memberJoin_excl.spec : Prop := ∀ γ urls urls', urls.Perm urls' →
  memberJoin (GF := GF) γ urls ∗ memberJoin γ urls' ⊢ iprop(False)

def urlsRight_excl.spec : Prop := ∀ γ urls urls', urls.Perm urls' →
  urlsRight (GF := GF) γ urls ∗ urlsRight γ urls' ⊢ iprop(False)

/-- **K1: a new cluster** of the members `ms` (each with the id `bootstrap` computes:
`Membership.initialMembers`), their peer hosts `hs m` reserved (2f's closed world), the members'
shared apply configuration `mc`: the state, one start token per member, the network, the
protocols with which the program serves each member's raft handler. The initial URL sets are
spent (no `urlsRight` for them). -/
def cluster_alloc.spec : Prop := ∀ (ms : List Member) (hs : Member → List GoString) (mc : ApplyCfg)
    (E : CoPset),
  (∀ m ∈ ms, Rafthttp.urlsHosts m.peerURLs = some (hs m)) →
  ([∗list] m ∈ ms, [∗list] a ∈ hs m, Http.addrFree (GF := GF) a) ⊢
    |={E}=> ∃ (γ : Cluster) (ν : Rafthttp.Net GF), etcdState γ (State.init ms) ∗ srvNet γ ν ∗
      clusterApplyCfg γ mc ∗
      ([∗list] m ∈ ms, memberBoot γ ms m ∗
        [∗list] a ∈ hs m, Http.protoAt a (Rafthttp.raftProto ν))

/-- **A new peer-URL set** for a member to be added: its hosts reserved for the cluster's network;
the right to give it to a member (once) and the right to join as that member (once). -/
def urls_reserve.spec : Prop := ∀ (γ : Cluster) (ν : Rafthttp.Net GF) (urls hs : List GoString),
  Rafthttp.urlsHosts urls = some hs →
  srvNet γ ν ∗ ([∗list] a ∈ hs, Http.addrFree (GF := GF) a) ⊢
    |==> urlsRight γ urls ∗ memberJoin γ urls ∗ [∗list] a ∈ hs, Http.protoAt a (Rafthttp.raftProto ν)

/-- **Start a member of a new cluster**: its boot token and a fresh directory, under a
configuration of a new cluster whose initial members are the allocated ones. -/
def memberStart_new.spec : Prop :=
  ∀ (γ : Cluster) (ms : List Member) (m : Member)
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (c : Config.Model),
  cfg.NewCluster' = true → m ∈ ms → m.name = cfg.Name' →
  (Membership.initialMembers cfg.InitialClusterToken' c.initialCluster).Perm ms →
  memberBoot (GF := GF) γ ms m ∗ dataDirFresh (Config.dirsOf cfg) ⊢ memberStart γ cfg c (some m.id)

/-- **Join as the member added with the configuration's peer URLs** (listed under the
configuration's own name in the initial-cluster map): its join right and a fresh directory. -/
def memberStart_join.spec : Prop :=
  ∀ (γ : Cluster) (urls : List GoString)
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (c : Config.Model),
  cfg.NewCluster' = false → urls.Perm c.peerURLs →
  (∃ u, c.initialURLs cfg.Name' = some u ∧ u.Perm c.peerURLs) →
  memberJoin (GF := GF) γ urls ∗ dataDirFresh (Config.dirsOf cfg) ⊢ memberStart γ cfg c none

/-- **Restart a stopped member** on its directories (any configuration but
`--force-new-cluster`: R1's `RestartNode` Margin). -/
def memberStart_restart.spec : Prop :=
  ∀ (γ : Cluster) (id : Nat) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (c : Config.Model),
  cfg.ForceNewCluster' = false →
  memberDisk (GF := GF) γ id (Config.dirsOf cfg) ⊢ memberStart γ cfg c (some id)

/-- Split the closers off a built server (embed's error path: `Cleanup` before `Start`). -/
def srvBuilt_closers.spec : Prop := ∀ s γ id cfg,
  srvBuilt (GF := GF) s γ id cfg ⊢ srvClosers s (Config.dirsOf cfg)

end vocab

end EtcdServer
end EtcdGrove
end Perennial
