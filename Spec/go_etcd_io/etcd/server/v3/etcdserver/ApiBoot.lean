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
cannot share an address: round 1, provability F3); no shared apply configuration (members may be
configured differently: 2d's `srvCfg`, a member's own 3a `Apply.MemberCfg`). It gets
`etcdState γ (State.init ms)` in full, one `memberBoot γ ms m` per initial member, the cluster's
raft network `srvNet γ ν` (2f's `Net`) and, for each reserved host, the persistent
`Http.protoFam a (Rafthttp.raftFam ν)`, the run's family of protocols with which the program serves
the member's raft handler (in each generation `Http.protoFam_at` gives `Http.protoAt a
(Rafthttp.raftProto ν)`; second crash pass: net/http's protocols are per generation).

**A member's files** are keyed by its directories (`Config.Dirs`). At program start a directory
is `dataDirFresh ds` (the adequacy theorem's per-directory token: the paths pairwise distinct for
the whole run, canonical, no other string naming one of them: the axiom sweep's B3-1; to be listed
in W0's adequacy statement). **Round 2 (crash restart): the durable state is client-owned
throughout**, split as raft's durable node API: `diskState γ ds k` (exclusive, timeless) is what the
directories hold, of kind `k` (`DiskKind`: a new member's fresh directory, a joiner's, or member
`id`'s files); the program keeps it in its crash invariant, and a running server reaches it only
through the persistent access `diskAcc γ ds` (an update it fires at each durable write: the WAL's
`Save`, `SaveSnapshot`, the backend's commits, the snapshot installs). `diskIdle γ ds k`
(exclusive, volatile) says no server runs on `ds`: the start takes it, `HardStop`/`Stop` give it back
(`memberDisk γ id ds` is its name at a member's files), and **after a crash**, at any point of the
disk's life, `disk_crash` takes the disk's state with the old generation's `crashed` and gives the
next generation the disk, idle, at whatever kind the crash left (verify round, crash pass: R-A8
N4). `disk_new`/`disk_join` turn a fresh directory and a start token into a disk.

**Peer-URL sets are single-use** (round 1, provability F4). `urls_reserve` turns the addresses of a
new URL set into W0's `urlsRight γ urls` (`EtcdModel`, moved there by I1) and `memberJoin γ urls`. Every request that gives a member a
URL set takes its `urlsRight` (`EtcdServer.AddMember`, `UpdateMember`); the initial members' are
spent by `cluster_alloc`. So a URL set names at most one member over the cluster's life, and a
joiner holding `memberJoin γ urls` runs as the member added under `urls` (`bootstrap` assigns the
id the cluster has for those URLs, `ValidateClusterAndAssignIDs`): no `MemberUpdate` can move
another member onto them. Cost: a removed member's URL set cannot be used again (a scope
restriction, `batch-2e.md` Q1).

**Starting a member** (`NewServer`, K2) takes `memberStart γ cfg c oid` (`oid`: the member id when
it is known before the start), introduced by one law, `memberStart_disk`: the disk's access, its
idle token at kind `k`, and a configuration `k` admits (`diskCfgOk`): a new member's (`.boot ms m`:
`NewCluster`, the allocated initial members), a joiner's (`.join urls`: `NewCluster` false, the
configuration's peer URLs), any for member `id`'s files (`.member id`: a WAL; etcd ignores
`NewCluster`) but `--force-new-cluster`; in every kind `UnsafeNoFsync` false (the crash rule needs
fsynced writes).
It also takes `envUpd γ ecfg` (W0's), the
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

**Serving clients at an address** (repair3-boot: the relay's requests 1 and 2; second crash pass:
F-server-boot F3, F5). A member's client address `ep` is bound to one member of a cluster for the
whole run: `srvEp_reserve` turns the environment's `Http.addrFree ep` into the address's protocol
family (`Http.protoFam ep F`: the program picks `F L := Grpc.grpcOver (etcdContract γ ep at the heap
⟨g, L⟩) _`, so that in each generation `Http.protoFam_at` gives that generation's `Grpc.addrAt ep
(etcdContract γ ep)`) and `srvEp γ ep id` (persistent, agreeing in `id`, the same at every
generation: `srvEp_gen`). `srvAt s γ ep` (2c's lease specs and 2a's `Server.spec` take it) is
transparent: `srvFields s γ id ∗ srvEp γ ep id`. So a member restarted at its address (a new server
object `s'`, after a stop or a crash) is at it again from its own `srvFields`, while no other member
of `γ` ever is: W0's `leaseViewLb γ ep` is a view of member `id`'s lessor, which only moves forward
over the member's life in a generation (a stop's `Close` commits the batch: `backend.go:470-471`,
and the restart's lessor is recovered from that backend). It is not carried across a crash (no
`leaseViewLb_gen`: the batch a crash loses may hold applied grants), and it need not be: **the
contract the address serves is the generation's** (net/http's protocols are per generation, the
family set once: a crash kills every client of the old contract, and no request crosses it), so a
restarted member serves the next generation's contract, whose lease rows name that generation's
views, never the dead one's (F-server-boot F3: with one protocol for the run, built at the first
generation's heap, the restarted member could serve neither). The cost: a client address serves one
member id over the run (as peer-URL sets). `leaseURLOf_intro`
gives 4b's `Leasehttp.leaseURLOf γ ep (u ++ "/leases/internal")` for the peer URLs `u` of `ep`'s
member, under the existing deployment premise `Leasehttp.leasePeerURL` of that URL; W0's
`peerLeaseServed γ` (every member's peer URLs serve its lease handler: what 2c's forwarded
`TimeToLive` row is gated on, verify-round F1) is introduced for a one-member cluster under that
premise of its member's peer URLs (`peerLeaseServed_intro`) and eliminated into `leaseURLOf`
(`peerLeaseServed_url`).

## Intended realization

* `Cluster` holds raft's cluster names (`Raft.Cluster`, `dup = false`: 2d), the raft network `ν`
  (2f's `Net`, its `img`/`dbIn` the server's: a database image of the committed state through `i`;
  `dbIn id i`, **member `id`'s snapshot directory has saved a file of index `i` of a certified image**,
  a persistent fragment of a generation-independent record per member, the history of saves of the
  directory member `id`'s disk names, whose authority the directory's invariant holds and
  `saveOk ν id sd`'s commit extends; with the member's deletion right `snapDel` the install knows the
  file is still there: second crash pass, F-server-boot F4, `dbIn` keyed by the receiver and built
  from global vocabulary only, since `ν` is the same at every generation, `srvNet_gen`), the URL-set
  authority, the client-address map (`srvEp`'s: `ep ↦ id` in an invariant at `srvEpN`, each entry
  holding its `Http.protoFam`; second crash pass, F-server-boot F5); `etcdState` is 2c/2d's. The bridge to 2d's server-level `Names` (`.etcd = γ`) is `isServer_names`/
  `srvMember_node` (W0 declined making `Cluster` a structure: the client API's ghost name stays
  opaque); the realization fixes one `Names` per `Cluster` (`srvNode_agree`).
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
* `diskState γ ds k`: per kind, the fresh directory with its start token (`memberBoot`, or
  `memberJoin`'s reserved vacancy), or the member's files as `memberDisk` used to be (above), with
  the in-flight batch, **at every step of the disk's life** (see "Crashes"); `diskIdle γ ds k`: the
  fragment of `k` frozen while no server runs, with raft's `nodeVacant` for a member's files.
  `diskState` carries a per-disk generation record (the name `g` of `hG`'s crash token) and
  `diskIdle` at `hG` is **its token for `g` or `g`'s `crashed`**, as raft's vacancy
  (`Raft.raftState_gen`'s section; verify-round F-server-boot F1, F-raft-storage F1): `disk_crash`
  must hold at every `L'`, also one whose crash name was used before (the current one included,
  where its idle token is already out), so it gives the pool's token for a new name and the
  recorded `crashed` for a used one. Hence `diskIdle_excl`, `diskIdle_agree` and `memberDisk_excl`
  give `crashed` as their alternative: `NewServer`'s first step (its `notCrashed`) refutes it.
* `memberStart γ cfg c oid`: `memberStart_disk`'s left side at its conditions.
* `srvFields s γ id` (re-review RR2): the literal's read-only fields (`memberID`, `cluster`,
  `lgMu`/`lg`, `readych`, `Cfg` but `SnapshotCount`/`SnapshotCatchUpEntries`), `⌜0 < id < 2 ^ 64⌝`;
  made right after the server literal in `NewServer`.
* `srvMember s γ id`: `srvFields s γ id`, the transport (`r.transport`, set last in `NewServer`:
  2f's `isTransport` of `ν` and `id`), 2d's `srvNode` (`srvMember_node`).
* `srvBuilt s γ id cfg`: one conjunct per subsystem (the slot convention): the raft node and its
  storage (2d), the backend, its hooks and the consistent index (4a, 2d), the lessor (3c), the KV
  store (3e), the auth store (3d), the alarm store, the compactor, the membership view, the
  transport (2f), `Cfg`'s two fields `start` defaults (`SnapshotCount`, `SnapshotCatchUpEntries`:
  exclusive until `start`), `envUpd γ ecfg`, and the node's running token for `id` (hence
  `srvBuilt_excl`). The member's files stay in `diskState`, which the server reaches through
  `diskAcc` (verify round, crash pass: they used to move into the running server's invariant, out of
  the crash law's reach).
* `isServer s γ`: the request path's invariant (2c) and the fields `start` sets (`Cfg`'s two
  defaulted fields among them, read-only from then on); `srvGate s q`: a
  fractional token of the store's and the backend's readers (3e's, 4a's reader tokens), which the
  stop's census rebuilds into the backend's whole open token for `Cleanup`.
* `srvRunning s γ id ds`: the right to send on `s.stop`, with the escrow of `s.done`'s closing:
  `run`'s stop deposits 2d's `srvStopped`, which with `Cleanup`'s `srvClosed` is `memberDisk`
  (2d's `srvStopped_disk`).

## Crashes (verify round, crash pass: R-A8 N1, N2, N4)

**One crash law per disk, at every point of its life** (`disk_crash`): from `diskState γ ds k`, the
old generation's `crashed` and the OS's crash rest (`crashRest`, the disk's files taken out of it:
`diskFiles ds`), under the environment premises `ServerStorage.diskOk` and `Wal.crashInScope`, the
next generation `L'` gets the disk, **idle** (the crash killed every thread) and at the kind the
crash left (second crash pass, F-server-boot F2: no out-of-scope case, "Scope" below). Whether a
server ran is the realization's, not the law's: there is no `crashGone`, and `diskIdle` is not a
premise (R-A8 N4: `crashGone` came only from a running server's `srvRunning`, so a crash inside
`NewServer`/`bootstrap`, before `Start`, inside `HardStop`/`Cleanup` or after `Cleanup` found
nothing to apply). The law holds at each of those points because **every durable resource is in
`diskState` at every step**: every durable write goes through `diskAcc` at its atomic point, and a
write that is not atomic on disk has two updates with the in-flight state between them in the disk
(the WAL's `walWriting`, `SaveDBFrom`'s `snapSaving`, the install's rename inside
`Snap.dbFile_rename`'s update, which also moves the revert list).

**Realization** (`diskState`, per kind):
* `.boot ms m`: `memberBoot γ ms m`, the backend file (absent, closed `Backend.beFile p o`, or open
  `beDurInv γb p ∗ beSynced γb ∗ beHist γb L`) with its revert state `beRevs p os`, no WAL;
* `.join urls`: `memberJoin γ urls`, the same backend file states, no WAL;
* `.member id`: the WAL (`Wal.walRecs (walDirOf ds) R`, or `walWriting R w` while a write is in
  flight), raft's `raftState γ.raft id D` with `walHolds R D` and, while a batch is in flight, its
  unfired `readyEnter` (deposited before `Save`, fired at its synced write: the raft loop's), the
  backend file (closed from `bootstrap`'s start to `OpenBackend`'s open and from `Close`'s on; open
  from `New`'s allocation step to `Close`), its revert state (with `none` while a file `bolt.Open`
  created has no durable name: 4a's `beOpenUpd`, second crash pass G-a), during an install the old
  backend renamed over while open (its history and `Backend.beDetached`, until its `Close`: second
  crash pass G-b), the snapshot dbs' deletion right.
The snapshot directory's invariant (`snapDbs`/`snapSaving` with `snapGone`, allocated from
`dataDirFresh`, keyed per generation) is beside it; `disk_crash` opens it. The record behind 2f's
`ν.dbIn id i` (the directory's history of saves) is not keyed per generation (second crash pass,
F-server-boot F4: `ν` is the same at every generation, so its meaning must be too): a save's record
is made at `SaveDBFrom`'s directory fsync (durable), its authority moves with the invariant across
the crash, and only the member's own deleter (`snapDel`) removes such a file.

The crossing: the WAL by `Wal.walRecs_crash`/`walWriting_crash` (records `R'`, meeting
`R'.crashScopeOk` under `Wal.crashInScope`); raft's state by
`Raft.raftState_gen` (no batch in flight) or `Raft.raftState_crash` (the deposited `readyEnter`; `D'`
the restart view of `R'`: `R.crashedDuring w R'`'s cases are `D.crashOk b D'`'s, and
`R'.confAboveOk` gives `D'.confAboveOk`), each giving `raftState` and `nodeVacant` at `L'`; the
backend by 4a's `Backend.beFile_crash` (closed) or `beCrash` (open), each taking the file out of
`crashRest`, after a detached old backend is folded into the revert list (`Backend.beDetached_crash`); the snapshot directory by `Snap.snapDbs_crash`/`snapSaving_crash`; `memberBoot` and
`memberJoin` by their crash laws (raft's crossing of the reserved durable state and vacancy,
`Raft.global` for their persistent facts, 2f's `Rafthttp.peerAddr_gen` for the addresses); then
`diskState` and `diskIdle` at `L'` (with `nodeVacant` in `diskIdle` for a member's files). **The kind
changes** only from `.boot`/`.join` to `.member id`, at the WAL's creation (`wal.Create` writes a
temporary directory, renames it onto the WAL's path and fsyncs the parent before returning: a crash
before the rename's fsync leaves no WAL, nothing of raft started, the kind unchanged).

**Scope** (second crash pass, F-server-boot F2; R-A8 N2 before it). The covered crashes are those
after which **the WAL a restart reads** (2e's trusted `walRecs`: what `Open` + `ReadAll` return)
**meets `Wal.Recs.crashScopeOk`**: at most one conf-change entry above the stored commit (R1's
`Durable.confAboveOk`; `issues/raft-commit-lost-with-entries-kept.md`, a reproduced raft safety bug;
the alternative is a raft/etcd fix), and no snapshot record above it (a crash after a received
snapshot's WAL record and before its batch's state record). That is W0's environment premise, the
opaque `Prop` `Wal.crashInScope` ("every crash of the run leaves each WAL meeting `crashScopeOk`"),
which the WAL's crash laws take and turn into `⌜R'.crashScopeOk⌝` of the records they give, and
which `disk_crash` takes beside `ServerStorage.diskOk`, so the adequacy proof needs no case for a
crash out of scope (round 2's transparent `crashOutOfScope` disjunct was not vacuous, but no proof
could refute it, so K6 could not be proved: F-server-boot F2). The user's decision (`batch-2e.md`
Q2, open question 2.8). Margin: an at-rest crash of a lagging follower whose WAL holds two conf
changes above its commit is also out of scope by this premise, though raft handles it
(`raftState_gen` has no `confAboveOk` premise); telling it apart needs the record order (the state
record after the entries) in `Wal.Recs`. `diskState` keeps **no** conf-entry bound (round 2's header
claimed one: false, a lagging follower's WAL holds committed entries with several conf changes
above its stored commit, open question 2.8; R-A8 N2, S4).

**A first boot's backend file may vanish (second crash pass, G-a; pending the user).** `bolt.Open`
creates `member/snap/db` and nothing syncs `member/snap` until a received snapshot's `SaveDBFrom`, so
4a's revert list holds `none` for it and a crash may lose it; a restart after the member's first
local snapshot then panics (`nonissues/etcd-backend-name-lost-restart-panic.md`). `disk_crash`'s
realization needs the user's decision there (`disk_crash`'s docstring).

**How the program reaches `diskState` at a crash (a gap, recorded).** Perennial's crash frame is
proved at boot and gets only invariants and its own closure (`CrashAdequacy.lean`). The program
keeps `diskState` in its invariant, the running server opens it through `diskAcc` inside callees'
atomic updates (the WAL's, the snapshotter's, the backend's), and the frame must take it out for
`disk_crash`. An accessor fired inside a callee's atomic update cannot rule out that the frame took
it: that needs the generation's `notCrashed`, which only a step owns (its state interpretation).
Needed from Perennial: a crash-aware invariant (opened at a thread's step, which refutes `crashed`,
and handed whole to the crash frame), or durable callees whose atomic updates admit a `crashed`
answer, refuted at their step. The same holds of every crash law over client-owned durable state
here (4a's `beCrash` with `beHist`, 4c's `boltCrash` with `boltState`, the WAL's and the
snapshotter's crash laws). A graceful stop is the case with no crash (`HardStop`'s post).

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

`srvMember_persistent`, `srvMember_agree`, `srvMember_id`, `srvFields_persistent`, `srvFields_id`,
`srvMember_fields` (re-review RR2), `isServer_persistent`,
`srvGate_fractional`, `srvBuilt_excl`, `srvRunning_excl`, `srvBuilt_running_excl`,
`stoppingCh_persistent`, `doneCh_persistent`, `readyCh_persistent`, `srvNet_persistent`,
`srvNet_agree`, `srvNet_gen`, `diskState_timeless`,
`diskState_excl`, `diskIdle_excl`, `diskIdle_agree`, `memberDisk_excl`, `dataDirFresh_timeless`,
`dataDirFresh_excl`, `memberBoot_timeless`, `memberJoin_excl` (W0's `urlsRight_excl`), `cluster_alloc`,
`urls_reserve`, `disk_new`, `disk_join`, the crash laws `disk_crash`, `memberBoot_crash`,
`memberJoin_crash`, `dataDirFresh_crash` (verify round, crash pass), `memberStart_disk`,
`srvBuilt_closers`, `srvEp_persistent`, `srvEp_agree`, `srvEp_reserve`, `srvEp_gen`,
`srvAt_persistent`, `leaseURLOf_intro`, `soleMember_intro`, `peerLeaseServed_intro`,
`peerLeaseServed_url` (verify-round F1), and
the slots' introductions
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
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.Api
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.Api
public import Spec.go_etcd_io.etcd.server.v3.lease.Api
public import Spec.go_etcd_io.etcd.server.v3.auth.Api
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.Durable
public import Spec.go_etcd_io.etcd.server.v3.lease.leasehttp.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel

export EtcdServerPb (irrIsRevoke)

/-- **What a member's directories hold** (round 2): a fresh directory with an initial member's
start token, a fresh one with a joiner's (its peer URLs), or member `id`'s files (a WAL). -/
inductive DiskKind where
  | boot (ms : List Member) (m : Member)
  | join (urls : List GoString)
  | member (id : Nat)

/-- The member id a disk's kind names, if any. -/
def DiskKind.id? : DiskKind → Option Nat
  | .boot _ m => some m.id
  | .join _ => none
  | .member id => some id

/-- The namespace of the program's disk invariants (`diskAcc`'s mask). -/
def diskN : Namespace := nroot .@ "etcdDisk"

/-- The namespace of a cluster's client-address map (`srvEp_reserve`'s mask; second crash pass). -/
def srvEpN : Namespace := nroot .@ "etcdSrvEp"

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
opaque srvNet [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : Cluster) (ν : Rafthttp.Net GF) : IProp GF := iprop(True)

/-- **Nothing of etcd's is in the directories `ds`** (exclusive, timeless). -/
opaque dataDirFresh [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ds : Config.Dirs) : IProp GF := iprop(True)

/-- **Member `m` of the new cluster `γ` of initial members `ms` may start once** (exclusive). -/
opaque memberBoot [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : Cluster) (ms : List Member) (m : Member) : IProp GF := iprop(True)

-- `urlsRight γ urls` (the right to give a member of `γ` the peer URLs `urls`, once) is W0's
-- `EtcdModel.urlsRight` (moved there at integration I1, so that a client's `MemberAdd`/`MemberUpdate`
-- can take it); `urls_reserve` below mints it.

/-- **The member added with the peer URLs `urls` may join `γ` once, from a fresh directory**
(exclusive). -/
opaque memberJoin [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : Cluster) (urls : List GoString) : IProp GF := iprop(True)

/-- **The directories `ds` hold durable state of kind `k`** (exclusive, timeless; client-owned
for good, kept by the program in its crash invariant). -/
opaque diskState [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : Cluster) (ds : Config.Dirs) (k : DiskKind) : IProp GF := iprop(True)

/-- **No server runs on `ds`, whose disk is of kind `k`** (exclusive). -/
opaque diskIdle [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : Cluster) (ds : Config.Dirs) (k : DiskKind) : IProp GF := iprop(True)

-- (second crash pass, F-server-boot F2) `crashOutOfScope ds` is gone: `disk_crash` takes W0's
-- environment premise `Wal.crashInScope`, under which the WAL's crash laws give records meeting
-- `Wal.Recs.crashScopeOk`.

/-- The files of the disk `ds` whose crash-time contents `disk_crash` takes from the OS's crash
rest (`crashRest`): the backend's file (`member/snap/db`). -/
def diskFiles (ds : Config.Dirs) : List GoString :=
  [Config.backendPathOf ds.dataDir]

/-- **A server's access to the disk** (persistent): an invariant-style accessor at `diskN`, opened
at each durable write (the WAL's two updates, `walWriting` then `walRecs`, each through it; the
second fires the batch's `readyEnter`). Verify round (A8-provability F2): an atomic update at mask
`∅` blocked both the raft loop's write (firing `readyEnter` needs `↑γ.raft.ns`) and
`RestartNode`; with an accessor at `diskN`, raft's namespace (`etcdN .@ "raft"`, disjoint from
`diskN`) stays open. -/
def diskAcc (γ : Cluster) (ds : Config.Dirs) : IProp GF :=
  iprop(□ ∀ E : CoPset, ⌜↑diskN ⊆ E⌝ -∗ |={E, E \ ↑diskN}=> ∃ k : DiskKind, diskState γ ds k ∗
    (∀ k' : DiskKind, diskState γ ds k' ={E \ ↑diskN, E}=∗ True))

/-- **The directories `ds` hold member `id`'s files and no server runs on them** (a stopped
member: `HardStop`'s post). -/
def memberDisk (γ : Cluster) (id : Nat) (ds : Config.Dirs) : IProp GF :=
  diskIdle γ ds (.member id)

/-- **The right to start a member of `γ` with configuration `cfg`** (heap parts `c`), member
`oid` when known: exclusive; introduced by `memberStart_disk` (round 2). -/
opaque memberStart [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : Cluster) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (c : Config.Model) (oid : Option Nat) : IProp GF := iprop(True)

/-! ## The server object -/

/-- **`s`'s literal fields** (persistent; re-review RR2): the fields `NewServer`'s server literal
sets and nothing writes again: `memberID` (`id`), `lgMu`/`lg` (the read lock's field a zap logger),
`cluster` (2e's membership view of member `id`), `readych`, `Cfg`'s fields but the two `start`
defaults (`SnapshotCount`, `SnapshotCatchUpEntries`: `srvBuilt`'s until `start`, read-only after it:
2d's `srvStarted`), with `⌜0 < id < 2 ^ 64⌝`. What the getters `Logger`, `MemberID`,
`FeatureEnabled`, `RequestTimeout`, `Cluster`, `ClusterVersion` read: they are callable from the
literal on (`NewServer` itself, `Process` from `tr.Start()` on), before `srvMember`. -/
opaque srvFields [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s : Loc) (γ : Cluster) (id : Nat) : IProp GF := iprop(True)

/-- **`s` is the server object of member `id` of `γ`** (persistent): built by `NewServer`. -/
opaque srvMember [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s : Loc) (γ : Cluster) (id : Nat) : IProp GF := iprop(True)

/-- **The client address `ep` is member `id`'s of `γ`, for the whole run** (persistent; repair3-boot,
the relay's request 1): set once, by `srvEp_reserve`, from the environment's `Http.addrFree ep`. -/
opaque srvEp [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : Cluster) (ep : GoString) (id : Nat) : IProp GF := iprop(True)

/-- **Member `s` of `γ` answers the clients at endpoint `ep`** (transparent, persistent; was 2c's
provisional opaque in `ApiReq.lean`): `s` is a server object of the member `ep` is bound to. Every
server object of that member (a restart after a stop or a crash) is at `ep`; no other member is.
The bridge between 2c's member and W0's per-endpoint `leaseViewLb γ ep`, whose intended realization
is member `id`'s (2d's applied view: `leaseViewLb γ ep j` is `∃ id, srvEp γ ep id ∗` member `id`'s
lessor has reflected lease table `j` in this generation, the lessor only moving forward over the
member's life, restarts after a stop included). -/
def srvAt (s : Loc) (γ : Cluster) (ep : GoString) : IProp GF :=
  iprop(∃ id, srvFields s γ id ∗ srvEp γ ep id)

/-- **`s` is built from `cfg` and not started** (exclusive). -/
opaque srvBuilt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s : Loc) (γ : Cluster) (id : Nat)
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : IProp GF := iprop(True)

/-- **`s` serves `γ`** (persistent): started; the request path's handle. -/
opaque isServer [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s : Loc) (γ : Cluster) : IProp GF := iprop(True)

/-- **A share `q` of the right to call `s`'s request path** (fractional): every request-path call
holds a share for its duration; the stop takes it whole (no request in flight). -/
opaque srvGate [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s : Loc) (q : Qp) : IProp GF := iprop(True)

/-- **The right to stop `s`, member `id` of `γ` whose files are in `ds`** (exclusive). -/
opaque srvRunning [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s : Loc) (γ : Cluster) (id : Nat) (ds : Config.Dirs) : IProp GF := iprop(True)

/-- `ch` is a server's stopping channel (persistent): closed at most once, by the stop. -/
opaque stoppingCh [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ch : Loc) : IProp GF := iprop(True)

/-- `ch` is `s.done` (persistent): closed when `run`'s stop is over; a receive gives nothing (the
deposit stays for `srvRunning`). -/
opaque doneCh [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s : Loc) (ch : Loc) : IProp GF := iprop(True)

/-- `ch` is `s.readych` (persistent): closed once the member published itself; a receive gives
nothing. -/
opaque readyCh [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s : Loc) (ch : Loc) : IProp GF := iprop(True)

/-! ## Internal (the package's proofs) -/

/-- **The backend `be` at file `p`, closable**: 4a's handle with its whole open token and its
footprints, what `backend.Close` takes (verify round, server-boot's request: `OpenBackend` returns
what `backend.New` returns, so the provisional `ServerStorage.beOpen` is gone). Exclusive.
repair3-boot: the backend's names `γb` are a parameter (the closer passes 4a's `beCloseUpd γb p`,
whose history `beHist γb L` the client's crash state holds). -/
def beClosable (be : GoInterface) (p : GoString) (γb : Backend.BeNames) : IProp GF :=
  iprop(∃ (b : Loc) (Pk : IProp GF) (F G Fh : Backend.Fp) (V : Backend.Image),
    ⌜be = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #b⌝ ∗
    Backend.isBackend γb b p Pk ∗ Backend.beOpen γb 1 ∗ Backend.beVis γb F V ∗
    Backend.beNoVis γb G ∗ ⌜∀ c, F c ∨ G c⌝ ∗ Backend.beHookFp γb Fh ∗ ⌜Backend.Fp.disj F Fh⌝)

/-- `bootstrap`'s result `b` for member `id` of `γ` and configuration `cfg` (exclusive). -/
opaque bootOk [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (b : Loc) (γ : Cluster) (id : Nat)
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : IProp GF := iprop(True)

/-- `bootstrap`'s raft record `br` (exclusive). -/
opaque bootRaftOk [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (br : Loc) (γ : Cluster) (id : Nat)
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : IProp GF := iprop(True)

/-- The record `b` reaches the backend `be` through read-only fields (persistent). -/
opaque bootBackendAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (b : Loc) (be : GoInterface) : IProp GF := iprop(True)

/-- The right to close `s.readych` once (`publishV3`). -/
opaque srvPublish [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s : Loc) : IProp GF := iprop(True)

/-- The WAL purge's handle (persistent): the invariant holding `Wal.walPurgeRight` while no purge
runs. -/
opaque srvPurge [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s : Loc) : IProp GF := iprop(True)

/-- `cc` is `s`'s corruption checker over the hash storage `hs` (persistent). -/
opaque isCorruptionChecker [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (cc : Loc) (s : Loc) (hs : GoInterface) : IProp GF := iprop(True)

/-- What `Cleanup` closes (exclusive): the lessor's stop right, the KV store's closer with its
readers given back, the auth store's closer, the backend's whole open token, the compactor's handle. -/
opaque srvClosers [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s : Loc) (ds : Config.Dirs) : IProp GF := iprop(True)

/-- What `Cleanup` gives back (exclusive): the backend's file at rest (verify round, crash pass: in
`diskState`, closed; repair3-boot: deposited at 4a's `Close`'s release, through its `beCloseUpd` fired
inside `diskAcc`, which takes the open file's `beHist` out of the disk at the same step; before it the
disk holds that history, which 4a's `beCrash` takes, after it the closed file, `beFile_crash`'s). -/
opaque srvClosed [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ds : Config.Dirs) : IProp GF := iprop(True)

/-! ## Provisional names of other batches' vocabulary (replaced at integration) -/

/-- **Provisional (2d):** `rn` is the raft node `newRaftNode` built for member `id` of `γ` over the
storage `st`. Exclusive. -/
opaque raftNodeBuilt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (rn : Loc) (γ : Cluster) (id : Nat) (st : Loc) : IProp GF := iprop(True)

-- (integration I4) The provisional `transporterOk tp` is 2f's `Rafthttp.transporterOk tp ν id`.

-- (integration I4) `irrIsRevoke r b` is 3h's `EtcdServerPb.irrIsRevoke` (exported below).

/-- **Provisional (W0's metrics boundary):** `gv` is a usable `*prometheus.GaugeVec`. -/
opaque gaugeVecOk [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (gv : Loc) : IProp GF := iprop(True)

/-- **`ETCD_VERIFY` is unset for the whole run** (a program-start fact W0's adequacy lists; the
backend's verification hooks panic otherwise: the axiom sweep's batch 1): 4a's
`Backend.etcdVerifyUnset` (integration I4). Persistent. -/
def backendEnvOk : IProp GF := iprop(⌜Backend.etcdVerifyUnset⌝)

/-! ## Provisional slots (see the header) -/

/-- **Provisional slot (2d):** the raft node's configuration. -/
opaque raftNodeBootCfg (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : Prop

/-- **Provisional slot (2a):** K8's scope restrictions. -/
opaque v3rpcBootCfg (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : Prop

/-- **Slot (3e):** the store's configuration: 3e's `Mvcc.storeCfgOk` of the configuration's
compaction batch limit (integration I4). -/
def mvccBootCfg (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : Prop :=
  0 ≤ sint.Z cfg.CompactionBatchLimit'

/-- **Slot (4a):** the backend's program-start facts (4a's `Backend.envOk`: `ETCD_VERIFY` unset)
and its configuration: a quota of at most 8 GiB (bbolt maps `quota + quota / 10`), no
`MemoryMlock` (verify round, server-boot's request: `OpenBackend`'s new premises). -/
def backendBootRes (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : IProp GF :=
  iprop(Backend.envOk ∗
    ⌜sint.Z cfg.QuotaBackendBytes' ≤ 8 * 1024 * 1024 * 1024 ∧ cfg.MemoryMlock' = false⌝)

/-- **Slot (3c):** the lessor's configuration against the environment's lease mode: without lease
expiry in the environment, 3c's trusted deployment premise `Lease.leasesOutliveRun` (W0's K2; "from
3c", item 6; integration I4). The server's `LessorConfig` leaves the revoke rate `0` (3c's
`0 ≤ leaseRevokeRate`). -/
def leaseBootRes (_cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (ecfg : EnvCfg) :
    IProp GF := iprop(⌜ecfg.leaseExpiry = false → Lease.leasesOutliveRun⌝)

/-- **Slot (3d):** the token provider's configuration: the simple provider, or 3d's `jwtTokOk` of
the JWT options ("from 3d", item 11; integration I4: it takes the cluster). -/
def authBootRes (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (γ : Cluster) : IProp GF :=
  iprop(⌜cfg.AuthToken' = go!"simple"⌝ ∨ Auth.jwtTokOk γ cfg.AuthToken')

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

/-- The backend: `ETCD_VERIFY` unset (4a's `envOk_intro`), and the default quota or one of at most
8 GiB, no `MemoryMlock`. -/
def backendBootRes_intro.spec : Prop := ∀ cfg : go_etcd_io.etcd.server.v3.config.ServerConfig,
  sint.Z cfg.QuotaBackendBytes' ≤ 8 * 1024 * 1024 * 1024 → cfg.MemoryMlock' = false →
  backendEnvOk (GF := GF) ⊢ backendBootRes cfg

/-- The lessor: leases may expire in the environment (the mode without expiry needs 3c's
deployment premise: `batch-2e.md` Q6). -/
def leaseBootRes_intro.spec : Prop := ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (ecfg : EnvCfg), ecfg.leaseExpiry = true → ⊢ leaseBootRes (GF := GF) cfg ecfg

/-- Auth: the simple token provider (etcd's default). -/
def authBootRes_intro.spec : Prop := ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (γ : Cluster), cfg.AuthToken' = go!"simple" → ⊢ authBootRes (GF := GF) cfg γ

/-! ## Laws -/

/-- **The configurations a disk of kind `k` starts with** (`memberStart_disk`). -/
def diskCfgOk (k : DiskKind) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (c : Config.Model) :
    Prop :=
  cfg.UnsafeNoFsync' = false ∧
  match k with
  | .boot ms m => cfg.NewCluster' = true ∧ m ∈ ms ∧ m.name = cfg.Name' ∧
      (Membership.initialMembers cfg.InitialClusterToken' c.initialCluster).Perm ms
  | .join urls => cfg.NewCluster' = false ∧ urls.Perm c.peerURLs ∧
      ∃ u, c.initialURLs cfg.Name' = some u ∧ u.Perm c.peerURLs
  | .member _ => cfg.ForceNewCluster' = false

def srvMember_persistent.spec : Prop := ∀ s γ id, Persistent (srvMember (GF := GF) s γ id)

def srvFields_persistent.spec : Prop := ∀ s γ id, Persistent (srvFields (GF := GF) s γ id)

/-- The literal's member id is a non-zero `uint64` (as `srvMember_id`). -/
def srvFields_id.spec : Prop := ∀ s γ id,
  srvFields (GF := GF) s γ id ⊢ ⌜0 < id ∧ id < 2 ^ 64⌝

/-- A built member's literal fields (re-review RR2): `srvMember` includes `srvFields`. -/
def srvMember_fields.spec : Prop := ∀ s γ id,
  srvMember (GF := GF) s γ id ⊢ srvFields s γ id

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

def diskState_timeless.spec : Prop := ∀ γ ds k, Timeless (diskState (GF := GF) γ ds k)

def diskState_excl.spec : Prop := ∀ γ ds k k',
  diskState (GF := GF) γ ds k ∗ diskState γ ds k' ⊢ iprop(False)

/-- One idle token per disk while the generation runs (two give its `crashed`: the header's
`diskIdle`; verify-round F-server-boot F1: with `False`, `disk_crash` at the current generation
could not be realized). -/
def diskIdle_excl.spec : Prop := ∀ γ ds k k',
  diskIdle (GF := GF) γ ds k ∗ diskIdle γ ds k' ⊢ crashed

/-- While no server runs, the disk's kind is the idle token's, or the generation crashed (an idle
token minted by `disk_crash` at a crash name used before carries no kind; verify-round
F-server-boot F1). `disk_crash`'s post gives both at one kind. -/
def diskIdle_agree.spec : Prop := ∀ γ ds k k',
  diskState (GF := GF) γ ds k ∗ diskIdle γ ds k' ⊢ ⌜k = k'⌝ ∨ crashed

/-- One stopped member per member id while the generation runs (raft's vacancy is in each:
two give `crashed`, `Raft.exclusive`; verify-round F-server-boot F1). -/
def memberDisk_excl.spec : Prop := ∀ γ id ds ds',
  memberDisk (GF := GF) γ id ds ∗ memberDisk γ id ds' ⊢ crashed

def dataDirFresh_timeless.spec : Prop := ∀ ds, Timeless (dataDirFresh (GF := GF) ds)

def dataDirFresh_excl.spec : Prop := ∀ ds,
  dataDirFresh (GF := GF) ds ∗ dataDirFresh ds ⊢ iprop(False)

def memberBoot_timeless.spec : Prop := ∀ γ ms m, Timeless (memberBoot (GF := GF) γ ms m)

def memberJoin_excl.spec : Prop := ∀ γ urls urls', urls.Perm urls' →
  memberJoin (GF := GF) γ urls ∗ memberJoin γ urls' ⊢ iprop(False)

/-- **K1: a new cluster** of the members `ms` (each with the id `bootstrap` computes:
`Membership.initialMembers`), their peer hosts `hs m` reserved (2f's closed world), the members'
shared apply configuration `mc`: the state, one start token per member, the network, the
protocols with which the program serves each member's raft handler. The initial URL sets are
spent (no `urlsRight` for them). (Integration: no shared apply configuration: members may be
configured differently, 2d's `srvCfg` per member, 3a's TTL-variant histories.) Verify round
(A8-provability F4): the members' ids are non-zero and none of raft's local targets
(`LocalAppendThread`, `LocalApplyThread`: raft's `cluster_alloc` needs it; the program computes the
ids, `memberIdOf`, and a SHA-1 id equal to one is a 2^-63 chance etcd never checks:
`nonissues/etcd-member-id-raft-reserved.md`). A runtime `MemberAdd` of such an id (time-salted)
is the same chance, recorded there, not excluded by the model. Changes: verify-round (client-core's
RR-1 request, repair3-boot): the post also gives the whole `urlsReserve γ 1` (W0's right to reserve
peer-URL sets, which `urls_reserve` spends and `soleMember_intro` gives up); realization: the
token's ghost name is allocated with `γ`, the full fraction handed out. Changes: verify-round
(second crash pass, F-server-boot F3): each reserved host's protocol is the run's family
`Http.protoFam a (Rafthttp.raftFam ν)` (was `Http.protoAt a (Rafthttp.raftProto ν)`, now a
generation's: `Http.protoFam_at` gives it in each generation, so the program serves the raft handler
again after a crash); the allocation also allocates the cluster's client-address map (`srvEpN`,
F5). -/
def cluster_alloc.spec : Prop := ∀ (ms : List Member) (hs : Member → List GoString)
    (E : CoPset),
  (∀ m ∈ ms, Types.urlsHosts m.peerURLs = some (hs m)) →
  (∀ m ∈ ms, m.id ≠ 0 ∧ Raft.isLocalTarget (W64 m.id) = false) →
  ([∗list] m ∈ ms, [∗list] a ∈ hs m, Http.addrFree (GF := GF) a) ⊢
    |={E}=> ∃ (γ : Cluster) (ν : Rafthttp.Net GF), etcdState γ (State.init ms) ∗ srvNet γ ν ∗
      urlsReserve γ 1 ∗ ([∗list] m ∈ ms, memberBoot γ ms m ∗
        [∗list] a ∈ hs m, Http.protoFam a (Rafthttp.raftFam ν))

/-- **A new peer-URL set** for a member to be added: its hosts reserved for the cluster's network;
the right to give it to a member (once) and the right to join as that member (once). It spends a
share `q` of `urlsReserve γ` (not given back): every `urlsRight` comes from a share, so a holder of
the whole `urlsReserve γ 1` knows none was minted (`soleMember_intro`). Changes: verify-round
(client-core's RR-1 request, repair3-boot): takes `urlsReserve γ q`; realization: the cluster's
invariant holds the spent shares beside the minted rights (a minted `urlsRight` entry exists only
when the invariant's share is not the whole), so the whole share outside excludes any entry.
Changes: verify-round (second crash pass, F-server-boot F3): the hosts' protocol is the run's family
`Http.protoFam a (Rafthttp.raftFam ν)`, as `cluster_alloc`'s. -/
def urls_reserve.spec : Prop := ∀ (γ : Cluster) (ν : Rafthttp.Net GF) (urls hs : List GoString)
    (q : Qp),
  Types.urlsHosts urls = some hs →
  urlsReserve (GF := GF) γ q ∗ srvNet γ ν ∗ ([∗list] a ∈ hs, Http.addrFree (GF := GF) a) ⊢
    |==> urlsRight γ urls ∗ memberJoin γ urls ∗ [∗list] a ∈ hs, Http.protoFam a (Rafthttp.raftFam ν)

/-- **A new member's disk**: its boot token and a fresh directory. -/
def disk_new.spec : Prop := ∀ (γ : Cluster) (ms : List Member) (m : Member) (ds : Config.Dirs),
  memberBoot (GF := GF) γ ms m ∗ dataDirFresh ds ⊢ |==> diskState γ ds (.boot ms m) ∗
    diskIdle γ ds (.boot ms m)

/-- **A joiner's disk**: its join right and a fresh directory. -/
def disk_join.spec : Prop := ∀ (γ : Cluster) (urls : List GoString) (ds : Config.Dirs),
  memberJoin (GF := GF) γ urls ∗ dataDirFresh ds ⊢ |==> diskState γ ds (.join urls) ∗
    diskIdle γ ds (.join urls)

/-- **The raft network of a cluster does not depend on the local generation** (verify round, crash
pass: R-A8 N1): a restarted member is built over the same `ν`. Realization: an `own` of the cluster's
ghost names (`GooseGlobalGS`). -/
def srvNet_gen.spec : Prop := ∀ (L' : GooseLocalGS GF) (γ : Cluster) (ν : Rafthttp.Net GF),
  srvNet (GF := GF) γ ν ⊣⊢ srvNet (hG := ⟨hG.goose_globalGS, L'⟩) γ ν

/-- **A crash, at any point of the disk's life** (verify round, crash pass: R-A8 N1, N2, N4; the
header's "Crashes"): under the environment premises `ServerStorage.diskOk` and `Wal.crashInScope`,
the next generation `L'` has the disk, idle, of the kind the crash left (a fresh directory stays one,
or became member `id`'s files once the WAL was created), its files taken out of the OS's crash rest.
The in-flight states (a WAL write, raft's batch, a snapshot save, a pending rename, an open
backend) are resolved by their own crash laws (R1's `raftState_gen`/`raftState_crash`, the WAL's
`walRecs_crash`/`walWriting_crash`, the snapshotter's `snapDbs_crash`/`snapSaving_crash`, 4a's
`beFile_crash`/`beCrash`). Changes: round 2's `crashGone` premise (from a running server only) and
`diskIdle_crash` (an idle disk, with no `crashRest`: it could not produce the backend file) are
replaced by this one law; `crashOutOfScope` was transparent, over the WAL's records. Verify-round
(F-server-boot F1, F-raft-storage F1): statement unchanged; it holds at every `L'`, a crash name
used before included, by `diskIdle`'s realization (a token or the generation's `crashed`: the
header) and raft's crossings, which hold at every `L'`; `diskIdle_excl`, `diskIdle_agree`,
`memberDisk_excl` give `crashed` in place of `False`. Changes (second crash pass, F-server-boot F2):
takes `ServerStorage.diskOk` (the WAL's crash laws, which its realization applies, take it; it was
missing) and W0's environment premise `Wal.crashInScope`, and loses the `crashOutOfScope` disjunct
(no proof could refute it, so K6 and `ReqCrashRecover` could not be proved): the WAL's crash laws now
give `R'.crashScopeOk` under the premise. At `L' = L` it is still the identity on the disk (one
`diskState` consumed, one given; `crashRest` one-shot per file). **Recorded, pending the user (second
crash pass, G-a):** 4a's laws now say that a first boot's backend file, which `bolt.Open` created
with no directory sync since, may be gone after the crash (`beOpenUpd`'s `none` in the revert list);
the restart then replays the WAL from index `0` while it holds no snapshot record above `0`, but after
a local snapshot `bootstrap` panics (`recoverSnapshot`, `bootstrap.go:482`:
`nonissues/etcd-backend-name-lost-restart-panic.md`), so for such a disk no restartable `diskState`
exists and this law is not realizable there until the user picks a premise (a created file's name
durable at its first sync, ext4's and xfs's behavior), a scope restriction or a fork fix
(`verify/repair5-crash.md`, New decisions). -/
def disk_crash.spec : Prop := ∀ [HasExt osFsExt] (L' : GooseLocalGS GF) (γ : Cluster)
    (ds : Config.Dirs) (k : DiskKind) (Ps : List GoString),
  ServerStorage.diskOk → Wal.crashInScope →
  (∀ p ∈ diskFiles ds, p ∉ Ps) →
  diskState (GF := GF) γ ds k ∗ crashed ∗
    crashRest (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L')) Ps ⊢
    |={⊤}=> (∃ k', diskState (hG := ⟨hG.goose_globalGS, L'⟩) γ ds k' ∗
          diskIdle (hG := ⟨hG.goose_globalGS, L'⟩) γ ds k' ∗ ⌜k' = k ∨ ∃ id, k' = .member id⌝) ∗
      crashRest (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L')) (diskFiles ds ++ Ps)

/-- **A boot token crosses a crash** (verify round, crash pass: a program that allocated the cluster
and crashed before making the member's disk). Realization: raft's `raftState_gen` for the reserved
durable state and vacancy, `Raft.global` for the bootstrap log's facts, `Rafthttp.peerAddr_gen`
for the members' addresses. It consumes the token and gives one, so it holds at every `L'`, the
current generation's included (verify-round F-raft-storage F1: there it is the identity, the
vacancy inside the `crashed` alternative of raft's realization). -/
def memberBoot_crash.spec : Prop := ∀ (L' : GooseLocalGS GF) (γ : Cluster) (ms : List Member)
    (m : Member),
  memberBoot (GF := GF) γ ms m ∗ crashed ⊢ |={⊤}=> memberBoot (hG := ⟨hG.goose_globalGS, L'⟩) γ ms m

/-- **A join right crosses a crash** (verify round, crash pass: a URL set reserved before a crash,
its member joining after it). Realization: the URL set's entry in the cluster's invariant keeps the
reserved durable state and vacancy at the generation of the right's holder (a generation record,
as raft's); the law moves it to `L'` by raft's `raftState_gen`. It consumes the right and gives one,
so it holds at every `L'` (verify-round F-raft-storage F1). -/
def memberJoin_crash.spec : Prop := ∀ (L' : GooseLocalGS GF) (γ : Cluster) (urls : List GoString),
  memberJoin (GF := GF) γ urls ∗ crashed ⊢ |={⊤}=> memberJoin (hG := ⟨hG.goose_globalGS, L'⟩) γ urls

/-- **A fresh directory crosses a crash** (verify round, crash pass: a directory kept for a later
member). Realization: the adequacy theorem's per-directory token holds the OS's resources of the
directory's paths (no backend file: `osMeta p none`), which a crash leaves as they are
(`crashRest_take`); the WAL and snapshot directories are absent by the closed world (nothing else
writes them). -/
def dataDirFresh_crash.spec : Prop := ∀ [HasExt osFsExt] (L' : GooseLocalGS GF)
    (ds : Config.Dirs) (Ps : List GoString),
  (∀ p ∈ diskFiles ds, p ∉ Ps) →
  dataDirFresh (GF := GF) ds ∗ crashed ∗
    crashRest (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L')) Ps ⊢
    |={⊤}=> dataDirFresh (hG := ⟨hG.goose_globalGS, L'⟩) ds ∗
      crashRest (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L')) (diskFiles ds ++ Ps)

/-- **The right to start a server on a disk**: its access, its idle token, a configuration of
its kind. -/
def memberStart_disk.spec : Prop :=
  ∀ (γ : Cluster) (k : DiskKind) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (c : Config.Model),
  diskCfgOk k cfg c →
  diskAcc (GF := GF) γ (Config.dirsOf cfg) ∗ diskIdle γ (Config.dirsOf cfg) k ⊢
    memberStart γ cfg c k.id?

/-- Split the closers off a built server (embed's error path: `Cleanup` before `Start`). -/
def srvBuilt_closers.spec : Prop := ∀ s γ id cfg,
  srvBuilt (GF := GF) s γ id cfg ⊢ srvClosers s (Config.dirsOf cfg)

/-- **A one-member cluster, never grown** (client-core, recheck RR-1: W0's `soleMember`, open
question A4's single-member alternative): the boot token of the only initial member `m` (a
voter) and the whole right to reserve peer-URL sets give `soleMember γ`; the boot token is given
back. Since every member addition takes a `urlsRight`, which only `urls_reserve` mints from a share
of `urlsReserve γ`, no member is ever added (`examples/etcd/leaseexpiry`: `etcdstart.StartServer`
allocates one member and reserves no URL set). Its source: `cluster_alloc` gives `urlsReserve γ 1`
and `urls_reserve` spends a share (repair3-boot). Realization: the reservation invariant's spent
shares are empty (the whole share is outside), so no URL set is minted; `soleMember` is the
persistent invariant that holds the given-up `urlsReserve γ 1` with `memberBoot`'s persistent
record that the initial members were `[m]`. -/
def soleMember_intro.spec : Prop := ∀ (γ : Cluster) (m : Member) (E : CoPset),
  m.isLearner = false →
  memberBoot (GF := GF) γ [m] m ∗ urlsReserve γ 1 ⊢ |={E}=> memberBoot γ [m] m ∗ soleMember γ

/-! ## Serving at a client address (repair3-boot: the relay's requests 1 and 2) -/

def srvEp_persistent.spec : Prop := ∀ γ ep id, Persistent (srvEp (GF := GF) γ ep id)

def srvAt_persistent.spec : Prop := ∀ s γ ep, Persistent (srvAt (GF := GF) s γ ep)

/-- One member of a cluster per client address (was 2c's `srvAt_agree`, `s = s'` too: false of a
member restarted at its address, a new server object). Changes: verify-round (second crash pass,
F-server-boot F5): within one cluster (it also gave `γ = γ'`, which no user needs and nothing in
net/http's API can realize: only net/http's map is global to the run, and it holds no tag);
realization: the cluster's client-address map (`srvEp_reserve`), a ghost map `ep ↦ id` whose
persistent fragments agree. -/
def srvEp_agree.spec : Prop := ∀ γ ep id id',
  srvEp (GF := GF) γ ep id ∗ srvEp γ ep id' ⊢ ⌜id = id'⌝

/-- **Reserve a client address for member `id` of `γ`** (the serving start: `etcdstart`'s `Serve`,
embed's `serveClients`, before `v3rpc.Server` and `Grpc.start`): the environment's `Http.addrFree ep`
gives the address's protocol family, as `Http.reserve` does (the program picks `F L :=
Grpc.grpcOver (etcdContract (hG := ⟨hG.goose_globalGS, L⟩) γ ep) (P' L)`, whose current member,
`Http.protoFam_at`, is `Grpc.addrAt ep (etcdContract γ ep)` in each generation), and binds the
address to the member. With `srvFields s γ id` (any server object of `id`: `NewServer`'s), `srvAt s γ
ep`. Once per run, as `addrFree`. Changes: verify-round (second crash pass, F-server-boot F3, F5):
reserves a family (was one protocol for the run, built at the first generation's heap, which a
member restarted after a crash could not serve: F3); takes `srvNet γ ν` and opens the cluster's
client-address map at `srvEpN` (the old realization, a tag in net/http's map, had no source in
net/http's API: F5). Realization: `srvNet γ ν` holds the invariant `∃ M, ghost_map_auth γ.ep M ∗
[∗map] e ↦ _ ∈ M, ∃ F' L, Http.protoFam (hG := ⟨g, L⟩) e F'` (its body over the global ghost state
`g` only); `ep ∉ dom M`, since an entry's `protoFam ep F'` with `Http.protoFam_at` and the caller's
`addrFree ep` give `False` by `Http.addrFree_protoAt_excl`; then `Http.reserve`, insert `ep ↦ id`
and persist its fragment, `srvEp γ ep id`. -/
def srvEp_reserve.spec : Prop := ∀ (γ : Cluster) (ν : Rafthttp.Net GF) (ep : GoString) (id : Nat)
    (F : GooseLocalGS GF → Http.Proto GF) (E : CoPset),
  ↑srvEpN ⊆ E →
  srvNet (GF := GF) γ ν ∗ Http.addrFree ep ⊢ |={E}=> Http.protoFam ep F ∗ srvEp γ ep id

/-- **The binding is the run's** (crash pass): a member restarted after a crash serves at the same
address, as the same member, from its new `srvFields` (no `srvAt` crosses: `s` is the new
generation's), the next generation's contract (`Http.protoFam_gen`, `protoFam_at`). Realization: the
cluster's client-address map (`srvEp_reserve`: an `own` of a global name and an invariant whose body
names only the global ghost state, `GooseGlobalGS`). Changes (second crash pass): its realization
was over `Http.protoAt_gen` (withdrawn). -/
def srvEp_gen.spec : Prop := ∀ (L' : GooseLocalGS GF) (γ : Cluster) (ep : GoString) (id : Nat),
  srvEp (GF := GF) γ ep id ⊣⊢ srvEp (hG := ⟨hG.goose_globalGS, L'⟩) γ ep id

/-- **The lease endpoint of a peer URL of `ep`'s member is over its lessor** (repair3-boot, the
relay's request 2): for a member `m` of a state the cluster reached, `ep`'s member (`srvEp`), and a
peer URL `u` of `m`'s whose lease endpoint is an etcd member's (4b's trusted deployment premise
`leasePeerURL`, which `TimeToLiveHTTP` already takes: embed serves `etcdhttp.NewPeerHandler(lg, s)`,
which mounts `s.LeaseHandler()` = `leasehttp.NewHandler(s.lessor, s.ApplyWait)` at
`/leases/internal`, `etcdhttp/peer.go:44-71`, on the member's own peer listeners), the endpoint
`u ++ "/leases/internal"` is `leaseURLOf γ ep`. True: a peer URL set names at most one member over
the run (single-use sets: `cluster_alloc`, `urls_reserve`, `urlsRight`), so the handler at `u` is
member `m.id`'s, of some server object of that member, whose lessor is the one `leaseViewLb γ ep`
views (`srvAt`'s docstring). Realization: `leaseURLOf γ ep url := ∃ id, srvEp γ ep id ∗ ⌜leasePeerURL
url⌝ ∗` the cluster's URL-set entry of `url`'s set naming `id` (persistent once the set is given).
**Not true of this repository's starters**: `examples/lib/etcdstart` serves only `s.RaftHandler()`
on the peer address, so `leasePeerURL` is false of its URLs (a forwarded `TimeToLive` gets a `404`,
which `TimeToLiveHTTP` turns into `ErrLeaseNotFound`): no `leaseURLOf` there (repair3-boot). -/
def leaseURLOf_intro.spec : Prop := ∀ (γ : Cluster) (ep : GoString) (σ : State) (m : Member)
    (u : GoString),
  m ∈ σ.members → u ∈ m.peerURLs → Leasehttp.leasePeerURL (u ++ go!"/leases/internal") →
  srvEp (GF := GF) γ ep m.id ∗ etcdLb γ σ ⊢ Leasehttp.leaseURLOf γ ep (u ++ go!"/leases/internal")

/-- **A one-member cluster whose member serves its lease endpoint** (verify-round F1,
`verify/F-client-api.md`): with `soleMember γ` and the boot token of its only initial member `m`
(given back), if each of `m`'s peer URLs `u` is a lease endpoint (4b's deployment premise
`leasePeerURL (u ++ "/leases/internal")`: the starter serves `s.LeaseHandler()` on the peer address,
as embed's `etcdhttp.newPeerHandler` does; `examples/lib/etcdstart` does not), W0's
`peerLeaseServed γ`. True: under `soleMember γ` every state the cluster reaches has members `[m]`
with `m`'s peer URLs (no `MemberAdd`/`MemberUpdate`: neither has a `urlsRight`), so the realization's
`∀ σ m' u ep` is `leaseURLOf_intro` at `m`. -/
def peerLeaseServed_intro.spec : Prop := ∀ (γ : Cluster) (m : Member),
  (∀ u ∈ m.peerURLs, Leasehttp.leasePeerURL (u ++ go!"/leases/internal")) →
  soleMember (GF := GF) γ ∗ memberBoot γ [m] m ⊢ memberBoot γ [m] m ∗ peerLeaseServed γ

/-- **A served lease endpoint is over `ep`'s member's lessor** (verify-round F1): for a member `m` of
a state the cluster reached, `ep`'s member (`srvEp`), and a peer URL `u` of `m`'s, `peerLeaseServed
γ` gives `leaseURLOf γ ep (u ++ "/leases/internal")` (its realization, unfolded). -/
def peerLeaseServed_url.spec : Prop := ∀ (γ : Cluster) (ep : GoString) (σ : State) (m : Member)
    (u : GoString),
  m ∈ σ.members → u ∈ m.peerURLs →
  peerLeaseServed (GF := GF) γ ∗ srvEp γ ep m.id ∗ etcdLb γ σ ⊢
    Leasehttp.leaseURLOf γ ep (u ++ go!"/leases/internal")

end vocab

end EtcdServer
end EtcdGrove
end Perennial
