/-
# etcd's server: the apply thread and the raft node driver (batch 2d): the vocabulary

What the server's apply side (`server.go`: `run`, `applyAll`, `applySnapshot`, `applyEntries`,
`apply`, `applyEntryNormal`, `applyConfChange`, the snapshots and the raft log's compaction, the
merged snapshot) and its raft driver (`raft.go`: `raftNode`, its `Ready` loop) use and give.
Namespace `EtcdServer` (shared with 2c's request path and 2e's bootstrap: a shared `Api.lean` of
this directory, if 2c writes one, may take over the cluster-level part below at integration).

## The shape, in words

**The cluster (shared with 2c, 2e, 3a).** An etcd cluster's server-level names `γ : Names` tie the
client-observable cluster `γ.etcd` (`EtcdModel.Cluster`, W0's `etcdState`/`etcdLb`) to the raft
cluster `γ.raft` (R1's `committedOps`, `committedLb`, `confAt`, `snapsMade`, ...) and fix the
environment's configuration `γ.cfg` (W0's `EnvCfg`, the members' auto-compaction and lease expiry).
The cluster's invariant (under `EtcdModel.etcdN`) owns raft's client-side state (`committedOps`,
`confDecisions`, `snapsMade`, `readCtxs`) and the cluster's half of `etcdState γ.etcd σ`, and keeps
**the history of the committed log**: `histAt γ k σ` (persistent) says the model state after the
committed log's first `k` entries is `σ`. Each committed entry moves it by one step, chosen at the
entry's commit (inside the proposal's update that raft fires, R1's `node.Propose.spec`): a client
request's `Step` (firing the client's update, 2c's), an environment step (`envUpd`, for the
lessor's revocations, the compactor's compactions, the alarms, `publishV3`), or nothing (an empty
entry, a lease checkpoint, a cluster version). The step is **the apply's model** `applyStep mc σ e
σ' res` (provisional, 3a's: a function of the state and the entry, at the proposing member's
configuration `mc`), so the answer fixed at the commit is the one the proposer's apply computes later
(`answered γ k id res`, persistent). `histPropose` is the law that builds raft's proposal update from
a proposer's update over `etcdState` (2c's `processInternalRaftRequestOnce`, `configure`), and
`isServer_names` ties 2e's handle `isServer s γ` (over W0's `Cluster`) to these names. So **the history is the committed log's** (K6): a
snapshot, a restore and a restart continue the same `histAt`; the member's own position in it is
its applied index.

**A member.** `srvNode s γ id` (persistent): `s` is member `id`'s `*EtcdServer` as `NewServer` built
it (its raft node driver, membership, consistent indexer, stores, atomics, and their invariants:
`Process` may be called from then on); `srvStarted s γ id` (persistent): the fields `start` adds. `srvApplied s γ k` (persistent): the member has applied the committed
log's first `k` entries, so its KV store (and lessor, auth store, membership) is at least at
`histAt γ k` (2c's linearizable reads wait for it: `applyWait`). `srvRunTok s γ id` (exclusive):
what `start` hands `run` (2e builds it at `NewServer`/`start`). `srvStopped s γ id` (exclusive):
what a stopped member leaves (`run`'s `close(done)` announces it): the durable halves a restart
takes (the WAL's `raftState`, the backend's image, raft's `nodeVacant`), which 2e's restart consumes.

**The apply thread.** `applyThread s γ ep p` (exclusive): the apply thread's state, with the
`etcdProgress` record `ep` at `p : Progress` (applied index and term, the disk and memory snapshot
indices): the state machine (the uber-applier over mvcc, the lessor, auth, membership, alarms, the
consistent indexer) at `histAt γ ci` for its consistent index `ci ≥ p.appliedi` (always: every
applied entry past `ci` moves `ci` to it, a restart's backend is at or past the raft snapshot, an
installed image at or past its index; entries up to `ci` are replayed for the in-memory membership
only, `shouldApplyV3 = false`), and `ep.confState` listing the configuration at `ci`. R1's `nodeConf`
is the `Ready` loop's, lent to the apply thread with a batch that has conf changes and returned
through `notifyc` (round 1, F3). Passed from one `applyAll` job to the
next (`schedTail`, `pkg/schedule`).

**The raft node driver.** `isRaftNode r γ id n` (persistent): the `raftNode` at `r` wraps raft node
`n` of `γ.raft` (`isNode n γ.raft id`), its `MemoryStorage` attached (`nodeStorage n γ.raft (memStor
ms)`), its WAL storage (2e's), its transport (2f's), its channels with their protocols. `rnLoop r`
(exclusive): the `Ready` loop's token (R1's `nodeDriver`, the WAL's write half, the ready
handler's writers). `rnStopper r` (exclusive): the right to `stop()` it (`run`'s deferred
shutdown); `rnStopped r γ id`: what it leaves. `applyBatch r γ apv B ph` (exclusive): a batch `B` the
loop handed the apply thread through `applyc` (the `toApply` value `apv`), at phase `ph` (`false`:
its snapshot, if any, not installed yet). `nodeAdvanced r k`, `nodeSnapLb r k` (persistent): R1's
`appliedLb`/`storSnapLb` of the driver's node, which the apply thread needs for the raft log's
snapshot and compaction.

**Durability (K5) is the loop's order of writes**: the leader sends before its write (R1's
`readyCheck`), every member fires the batch's `readyEnter` at the WAL's `Save` (2e's: the update fires
at the write's sync, moving the WAL-held `raftState γ.raft id D`), and only then sends (followers)
and `Advance`s; an entry is applied only after raft committed it, which needs a quorum's durable
acknowledgements. A crash loses nothing raft's durable state has, and every answered step's entry is
in it on a quorum.

## Intended realization

* `Names`: `etcd`, `raft`, `cfg`, `mc` and the names of the history. The cluster's invariant owns
  raft's `committedOps γ.raft ops` only (raft fires nothing for its own fillers, and a proposal's
  update learns no index), so the history is kept **per operation**: a `mono_list` of states, one
  per element of `ops`, with the answers per operation (round 1, S3); `histAt γ k σ` and
  `answered γ k id res` translate a log index `k` to its operation position through `committedLb`
  (the fillers below `k`, which raft's `opsOf` drops, change nothing). The invariant also holds the
  cluster's half of `etcdState γ.etcd (last hist)`, raft's `confDecisions`/`snapsMade`/`readCtxs`,
  each made snapshot's point (`snapPoint`), and the read registry (`readTicket`).
* `srvNode s γ id`: the server's read-only fields (`s.r`, `s.w`, `s.applyWait`, `s.consistIndex`,
  `s.cluster`, `s.kv`, `s.lessor`, `s.authStore`, `s.alarmStore`, `s.beHooks`, `s.snapshotter`,
  `s.Cfg`, the channels) as persistent points-to's, the invariants of the atomics (`appliedIndex`
  with `srvApplied` of its value, `committedIndex` with a committed prefix at least that long,
  `term`, `lead`: any value), the `bemu` lock's invariant (the current backend, whose state machine
  is the apply thread's), `inflightSnapshots`, `envUpd γ.etcd γ.cfg` (persistent), and the cluster's
  invariant.
* `applyThread`: the `etcdProgress` points-to's, `Cindex.ciWriter` (with an agreement half of the
  indexer's state, whose authority is in one invariant the pre-commit hook also opens), the
  uber-applier's contract (3a's) at the server's state machine, `confAt γ.raft ci m` with
  `ep.confState` listing `m`, the snapshot indices with `storSnapLb`.
* `isRaftNode`/`rnLoop`/`rnStopper`/`applyBatch`: the loop's ghost driver state (R1's `nodeDriver`,
  `readyStor`), the `applyc` protocol (each batch's committed entries with `committedLb`/
  `deliveredLb`, its snapshot's `snapValid`, the `notifyc` handshake: the loop's `Save` before the
  apply thread's snapshot (the WAL's synced write), the apply thread's conf changes before the loop's
  `Advance`; `raftAdvancedC`'s close carrying R1's `appliedLb n` of the delivered log), `msgSnapC`'s
  payload (a `MsgSnap` the node sent: `msgPts`, `msgSent`), `readStateC`'s (`readState`).

## Laws

Persistence, timelessness, exclusivity; the history: `histAt_agree`, `histAt_lb` (W0's `etcdLb`:
K7's realization), `histAt_committed`, `histAt_of_committed`, `answered_agree`, `committed_types`,
`snapImage_point`, `snapPoint_agree`, `applyStep_fun`, `applyStep_reach` (3a's), `histPropose`,
`readCtx_register`, `readReg_register`, `readReg_get`; the member: `srvApplied_mono`,
`srvApplied_zero`, `srvApplied_hist`, `srvApplied_read`, `srvReadAt_mono`, `srvNode_raftNode`,
`srvNode_agree`, `srvNode_errorc`, `isServer_names`, `srvMember_node`, `srvRunTok_intro`,
`applyInit_ep`, `srvStopped_disk`, `isRaftNode_node`, `isRaftNode_storage`, `nodeSnapLb_stor`,
`nodeAdvanced_applied`, `rnInit_place`, `applyThread_at`, `applyThread_applied`, `applyBatch_terms`,
`applyc_recv` (with the cursor `applycPos`), `readStateC_recv`, `msgSnapC_recv`,
`procErr_forbidden`.

## Requirement snippets

`examples/specreq/etcdserverapply/`: `apply.go` (a write's waiter answered with the commit's answer;
`applyWait` gives the applied state; a conf change's waiter after raft advanced; the replay below the
consistent index), `snapshot.go` (snapshot and raft-log compaction at the applied index; the merged
snapshot at the applied index and term; installing a received snapshot), `restart.go` (a member
restarted from its durable state continues the history; a crash loses no answered write),
`raftnode.go` (the driver's write-before-send order; `ReadIndex`/`ReadState`; the transport's
inbound `Process`/`ReportUnreachable`/`ReportSnapshot`).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.State
public import Spec.go_etcd_io.raft.v3.Api
public import Spec.PkgInit.go_etcd_io.etcd.server.v3.etcdserver
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.Api
public import Spec.go_etcd_io.etcd.pkg.v3.schedule.Api
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Api
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.read.Api
public import Spec.go_etcd_io.etcd.pkg.v3.idutil.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI

/-! ## Ghost names -/

/-- The server's own ghost names (the history's, the answers'): opaque. -/
opaque HistNames : Type := Unit

/-- (provisional, 3a's) **The apply-relevant configuration** of the cluster's members (the leases'
minimum TTL, `nonissues/etcd-lease-ttl-differs-across-members.md`): fixed at the cluster's
allocation and **shared by every member** (round 1, the coordinator's decision on provability F1:
2e's `NewServer` takes it as a premise against the member's configuration). -/
opaque MemberCfg : Type := Unit

/-- **An etcd cluster's server-level names**: the client-observable cluster (W0's names), the raft
cluster under it (R1's names), the environment's configuration (every member configured alike, the
cluster contract), the members' shared apply configuration, and the history's own names. -/
structure Names where
  etcd : EtcdModel.Cluster
  raft : Raft.Cluster
  cfg : EtcdModel.EnvCfg
  mc : MemberCfg
  hist : HistNames

/-! ## Pure models -/

/-- **The apply thread's progress** (`etcdProgress` without its `confState`): the applied index and
term, and the indices of the last snapshot saved to disk and of the last one made in memory. -/
structure Progress where
  appliedi : w64
  appliedt : w64
  diskSnap : w64
  memSnap : w64

/-- **A batch the `Ready` loop hands the apply thread** (`toApply`): the delivered log's length
before it (`prev`), its committed entries (from index `prev + 1`), its snapshot, and the term of the
latest hard state handed out up to it (`raftTerm`, the merged snapshot's guard). -/
structure ApplyBatch where
  prev : Nat
  ents : List Raft.LogEntry
  snap : Option Raft.Snapshot
  term : w64

/-- The applied index once the batch's snapshot (if any) is installed. -/
def ApplyBatch.base (B : ApplyBatch) : Nat :=
  match B.snap with
  | some s => uint.nat s.index
  | none => B.prev

/-- The delivered log's length after the batch (raft hands out no committed entries with a
snapshot, R1's `BatchOk`). -/
def ApplyBatch.last (B : ApplyBatch) : Nat := B.base + B.ents.length

/-- (provisional, 3a's with 2e's membership and 3c, 3d, 3e) **The apply's model**: applying the
committed entry `e` to the model state `σ` under the cluster's shared configuration `mc` gives `σ'`
and the answer `res` (a function of `mc`, `σ` and `e`: `applyStep_fun`). For an entry no request waits on
(an empty entry, a checkpoint, a cluster version) `σ' = σ`. -/
opaque applyStep (mc : MemberCfg) (σ : EtcdModel.State) (e : Raft.LogEntry) (σ' : EtcdModel.State)
    (res : EtcdModel.Resp) : Prop

/-- The `ShouldApplyV3` of an entry at index `i` for a consistent index `ci`: whether its effects go
to the backend (`apply`, `server.go:1934`). -/
def applyV3 (ci i : Nat) : Bool := decide (ci < i)

/-! ## Resources -/

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
  {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
  [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
  [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-! ### The cluster (shared with 2c, 2e, 3a) -/

/-- **The model state after the committed log's first `k` entries is `σ`.** Persistent. -/
opaque histAt (γ : Names) (k : Nat) (σ : EtcdModel.State) : IProp GF := iprop(True)

/-- **The committed entry at index `k` is request `id`, answered `res` at its commit.**
Persistent. -/
opaque answered (γ : Names) (k : Nat) (id : w64) (res : EtcdModel.Resp) : IProp GF := iprop(True)

/-- **Snapshot `s` was made with its configuration at point `a`** (persistent; recorded at
`snap_make` by its maker: `snapshot()` at `a = ci`, `createMergedSnapshotMessage` at the sender's
consistent index): `s.index ≤ a`, the configuration at `a` is `s.conf`'s, and the image sent with
it holds the state machine at `histAt γ a` (round 1, provability F3/F4: keyed by the snapshot, not by
its index). -/
opaque snapPoint (γ : Names) (s : Raft.Snapshot) (a : Nat) : IProp GF := iprop(True)

/-- **The database image installed with snapshot `s`**: the `.snap.db` of `s.index` holds the state
machine at the snapshot's point (`snapPoint γ s a`, `histAt γ a`), its stored consistent index `a`.
What the member's invariant over its snapshot directory gives a batch's snapshot (from 2f's
`recvd`/`dbIn` at `Process`), and what `applySnapshot` opens. Persistent. **Scope** (round 1, F4;
`nonissues/etcd-merged-snapshot-same-index-image.md`): the file is keyed by the index only, so this
holds only if a member never saves two merged snapshots of one index with different points before
installing one: an open question for the user. -/
opaque snapImage (γ : Names) (s : Raft.Snapshot) : IProp GF := iprop(True)

/-- (2f's `Img`, the server's choice at `net_alloc`) **`img` is an image for index `i`**: the state
machine at `histAt γ a` with stored index `a`, for a snapshot `s` of index `i` with `snapPoint γ s a`.
Persistent. -/
opaque imgAt (γ : Names) (i : w64) (img : Snap.BeImage) : IProp GF := iprop(True)

/-- **`ν` is the cluster's network** (2f's `Net`) with the server's meanings: `ν.γ = γ.raft`,
`ν.img = imgAt γ`, and `ν.dbIn i` the member invariant's record that its snapshot directory keeps
an image `imgAt γ i` (2e's `snapDbs`). Persistent. -/
opaque srvNet (γ : Names) (ν : Rafthttp.Net GF) : IProp GF := iprop(True)

/-- (provisional, 2c's read registry, item 5) **A registered read** under ticket `t`: a persistent
update over `etcdState` with relation `Rel` and result `Q`, registered when the committed log was
`l0`; the cluster's invariant fires it at every later history point, for each answer `Rel` allows,
and keeps the results for `readReg_get`. Exclusive (consumed by one `readReg_get`). -/
opaque readTicket (γ : Names) (t : Nat) (Rel : EtcdModel.State → EtcdModel.Resp → Prop)
    (Q : EtcdModel.State → EtcdModel.Resp → IProp GF) (l0 : List Raft.LogEntry) : IProp GF :=
  iprop(True)

/-- **The id space of member `s`'s request ids** (`s.reqIDGen`, 2c's `IdUtil`): its fresh ids are
fresh cluster-wide (the member id in the prefix, one prefix per run). Persistent. -/
opaque srvIdSpace (s : Loc) (γi : IdUtil.IdSpace) : IProp GF := iprop(True)

/-- **The member's reads are at or past `k`** (the slot for the read path, round 1 completeness F1):
a read of member `s`'s mvcc store (3e), lessor (3c) or auth store (3d), begun now, linearizes at a
history point `k' ≥ k` (`histAt γ k' σ'`) and answers as one of `Step`'s answers at `σ'`. Persistent.
**Provisional slot**: each subsystem's read spec is to be stated over it (requested in their `req/`
files); `srvApplied_read` introduces it. -/
opaque srvReadAt (s : Loc) (γ : Names) (k : Nat) : IProp GF := iprop(True)

/-! ### A member -/

/-- **`s` is member `id`'s server in cluster `γ`**, as `NewServer` builds it, from its server
literal on (before `tr.Start()`: `Process` may be called from then on): its raft node driver, the
membership, the consistent indexer, the stores' handles, the atomics and their invariants, `errorc`
(2f's `errChanOk`). Persistent. Member ids are `Nat`, as 2e's. -/
opaque srvNode (s : Loc) (γ : Names) (id : Nat) : IProp GF := iprop(True)

/-- **`s` is started** (persistent): the fields `start` sets (`s.w` with the request path's
registration predicate, 2c's; `s.applyWait` over `srvApplied s γ`; `s.stop`, `s.stopping`,
`s.done`; `s.ctx`; `s.read`; `s.leaderChanged`; the wait group behind `GoAttach`), read-only. -/
opaque srvStarted (s : Loc) (γ : Names) (id : Nat) : IProp GF := iprop(True)

/-- (provisional, 2e's `etcdhttp/types`) `err` is the `*httptypes.HTTPError` with status 403 that
`Process` returns for a refused message. Persistent. -/
opaque httpForbidden (err : GoInterface) : IProp GF := iprop(True)

/-- **Member `s` has applied the committed log's first `k` entries.** Persistent. -/
opaque srvApplied (s : Loc) (γ : Names) (k : Nat) : IProp GF := iprop(True)

/-- **What `start` hands `run`** for member `id` with directories `ds` (`srvRunTok_intro`).
Exclusive. -/
opaque srvRunTok (s : Loc) (γ : Names) (id : Nat) (ds : Config.Dirs) : IProp GF := iprop(True)

/-- **What a stopped member's apply side and driver leave** (`run`'s deferred shutdown, before
`Cleanup`): the WAL's durable half with `raftState`, the node's vacancy, the snapshot directory, the
history point of the backend's last commit. With 2e's `srvClosed ds`, the member's `memberDisk`
(`srvStopped_disk`). Exclusive. -/
opaque srvStopped (s : Loc) (γ : Names) (id : Nat) (ds : Config.Dirs) : IProp GF := iprop(True)

/-- **The apply thread's initial state, without its `etcdProgress`** (`run` allocates `ep`): progress
`p` (all at the `MemoryStorage` snapshot's index), the state machine at the consistent index `c ≥
p.appliedi`. Exclusive. -/
opaque applyInit (s : Loc) (γ : Names) (p : Progress) (c : Nat) : IProp GF := iprop(True)

/-- The writer's token of `s.appliedIndex` at value `a` (the apply thread's). Exclusive. -/
opaque appliedW (s : Loc) (a : w64) : IProp GF := iprop(True)

/-- The writer's token of `s.committedIndex` at value `c` (the `Ready` loop's, through the ready
handler). Exclusive. -/
opaque committedW (s : Loc) (c : w64) : IProp GF := iprop(True)

/-- The writer's token of `s.term` and `s.lead` (the apply thread's and the loop's: either may store
any value). Exclusive per field. -/
opaque termW (s : Loc) : IProp GF := iprop(True)
opaque leadW (s : Loc) : IProp GF := iprop(True)

/-! ### The apply thread -/

/-- **The apply thread's state**, with `ep` at progress `p`. Exclusive. -/
opaque applyThread (s : Loc) (γ : Names) (ep : Loc) (p : Progress) : IProp GF := iprop(True)

/-- (internal) **The apply thread inside `apply`'s loop**: the state machine applied through the
committed log's first `a` entries (its position `max a c`), the consistent index `c`, the applying
index `ai`; `ep`'s recorded progress still `p` (`applyEntries` stores the new applied index after
`apply` returns). `applyThread s γ ep p` is `∃ c ai, applyAt s γ ep p p.appliedi c ai`. Exclusive. -/
opaque applyAt (s : Loc) (γ : Names) (ep : Loc) (p : Progress) (a c ai : Nat) : IProp GF :=
  iprop(True)

/-- `s.forceDiskSnapshot`'s owner (the apply thread's; lent to the uber-applier, which calls
`ForceSnapshot` through its `SnapshotServer`). Exclusive. -/
opaque forceSnapW (s : Loc) : IProp GF := iprop(True)

/-! ### The raft node driver -/

/-- **`r` is member `id`'s raft node driver**, over raft node `n` (a `raftNode`). Persistent. -/
opaque isRaftNode (r : Loc) (γ : Names) (id : w64) (n : Loc) : IProp GF := iprop(True)

/-- **The `applyc` cursor** (exclusive): the next batch the apply side receives starts at delivered
length `k` (round 1, F2). -/
opaque applycPos (r : Loc) (k : Nat) : IProp GF := iprop(True)

/-- **A `raftNode` value fresh from `newRaftNode`**, for member `id` over node `n`: its channels new,
its node, storages and transport the configuration's, with their resources. Exclusive. -/
opaque rnInit (v : go_etcd_io.etcd.server.v3.etcdserver.raftNode) (γ : Names) (id : w64) (n : Loc) :
    IProp GF := iprop(True)

/-- **A driver configuration's resources** (`raftNodeConfig` value `cv`, the slot 2e's bootstrap
fills, `ApiBoot`'s `raftNodeBootCfg` being its configuration part): its `Node` is raft node `n` of
`γ.raft` with id `id` (R1's `isNode`, `nodeRunning`, `nodeDriver` at the start's driver state, the
apply side's `nodeConf`), its `raftStorage` that node's attached `MemoryStorage` (`nodeStorage n
γ.raft (memStor ms)`), its `storage` the member's WAL and snapshotter (2e's: holding `raftState
γ.raft id D` in its durable invariant, with `StorageHolds D` of the storage's contents), its
`transport` the member's (2f's), its `isIDRemoved` the membership's query, its logger. Exclusive. -/
opaque rnCfgOk (cv : go_etcd_io.etcd.server.v3.etcdserver.raftNodeConfig) (γ : Names) (id : w64)
    (n : Loc) : IProp GF := iprop(True)

/-- **The `Ready` loop's token.** Exclusive. -/
opaque rnLoop (r : Loc) : IProp GF := iprop(True)

/-- **The right to stop the driver** (its `stopped`/`done` channels). Exclusive. -/
opaque rnStopper (r : Loc) : IProp GF := iprop(True)

/-- **What a stopped driver leaves**: the raft node stopped (R1's `nodeStopped`, the id vacant again
once the node's run goroutine has exited), the ticker stopped, the transport stopped, the WAL closed
with its durable half (2e's: the `raftState γ.raft id D` the WAL holds). Exclusive. -/
opaque rnStopped (r : Loc) (γ : Names) (id : w64) : IProp GF := iprop(True)

/-- **The ready handler `rh` of server `s`** (`raftReadyHandler`: `getLead`, `updateLead`,
`updateLeadership`, `updateCommittedIndex` over `s`'s atomics). Persistent. -/
opaque readyHandlerOk (rh s : Loc) (γ : Names) : IProp GF := iprop(True)

/-- The ready handler's writers (`s.committedIndex`'s, `s.lead`'s): the loop's. Exclusive. -/
opaque readyHandlerTok (rh : Loc) : IProp GF := iprop(True)

/-- **A batch handed to the apply thread** (the `toApply` value `apv`), its snapshot installed
(`ph`) or not. Exclusive. -/
opaque applyBatch (r : Loc) (γ : Names) (apv : go_etcd_io.etcd.server.v3.etcdserver.toApply)
    (B : ApplyBatch) (ph : Bool) : IProp GF := iprop(True)

/-- **Raft has advanced past the delivered log's first `k` entries** at driver `r`'s node (R1's
`appliedLb n k`; a batch's `raftAdvancedC` closes with it). Persistent. -/
opaque nodeAdvanced (r : Loc) (k : Nat) : IProp GF := iprop(True)

/-- **Driver `r`'s `MemoryStorage` holds a snapshot at index `k` or later** (R1's `storSnapLb`).
Persistent. -/
opaque nodeSnapLb (r : Loc) (k : Nat) : IProp GF := iprop(True)

/-- `rac` is a batch's `raftAdvancedC`: closed once raft has advanced past the delivered log's first
`k` entries; a receive gives `nodeAdvanced r k`. Persistent. -/
opaque advancedAt (r rac : Loc) (k : Nat) : IProp GF := iprop(True)

/-- `ch` is driver `r`'s `applyc`. Persistent. -/
opaque rnApplyc (r : Loc) (ch : Loc) : IProp GF := iprop(True)

/-- `ch` is driver `r`'s `readStateC`. Persistent. -/
opaque rnReadStateC (r : Loc) (ch : Loc) : IProp GF := iprop(True)

/-! ### Values exchanged with other packages (provisional: their batches' vocabulary) -/

/-- (provisional, raftpb's, 3h) **`p` points to entry `e` at index `k`**, read-only for good (an
element of R1's `entriesRO`). Persistent. -/
opaque entryAt (p : Loc) (k : Nat) (e : Raft.LogEntry) : IProp GF := iprop(True)

/-- (provisional, the backend's, 4a) **`bs` is a backend snapshot** (`backend.Snapshot`) of the state
machine at a committed point `k`, with consistent index `k`. Exclusive (its `Close`). -/
opaque beSnap (bs : GoInterface) (γ : Names) (k : Nat) : IProp GF := iprop(True)

/-- (provisional, `io`'s and the snapshotter's, 2e) **`rc` is an `io.ReadCloser` streaming the
database image** of the state machine at committed point `k`. Exclusive. -/
opaque dbReader (rc : GoInterface) (γ : Names) (k : Nat) : IProp GF := iprop(True)

/-- (provisional, the lessor's, 3c) **`sl` lists expired leases `ids`** (`[]*lease.Lease`, from
`ExpiredLeasesC`), read-only. Persistent. -/
opaque expiredLeases (sl : GoSlice) (ids : List Int) : IProp GF := iprop(True)

/-- **`mg` is a merged snapshot message** (a `*snap.Message`): raft message `m` (a `MsgSnap` the
member may send: `msgSent`, its snapshot with `snapImage`) with the database reader of that image.
Exclusive (the transport consumes it). -/
opaque mergedSnap (mg : Loc) (γ : Names) (m : Raft.Msg) : IProp GF := iprop(True)

/-- `sl` is a `[]*raftpb.Message` of messages `msgs` the member may send (`msgSent` and `msgCredit` of
each, R1's), the slice and the messages owned (a response read-only: R1's `readyDq`). -/
def sendable (γ : Names) (sl : GoSlice) (msgs : List Raft.Msg) : IProp GF :=
  iprop(∃ ps : List Loc, ownSlice sl ps (DFrac.own 1) ∗ ⌜ps.length = msgs.length⌝ ∗
    [∗list] pm ∈ ps.zip msgs, Raft.msgPts pm.1 (Raft.readyDq pm.2) pm.2 ∗
      Raft.msgSent γ.raft pm.2 ∗ Raft.msgCredit γ.raft pm.2)

end vocab

/-! ## Laws -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
  {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
  [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
  [raft_sem : go_etcd_io.raft.v3.Assumptions]

def persistent.spec : Prop :=
  (∀ γ k σ, Persistent (histAt (GF := GF) γ k σ)) ∧
  (∀ γ k id res, Persistent (answered (GF := GF) γ k id res)) ∧
  (∀ γ s, Persistent (snapImage (GF := GF) γ s)) ∧
  (∀ γ s a, Persistent (snapPoint (GF := GF) γ s a)) ∧
  (∀ γ i img, Persistent (imgAt (GF := GF) γ i img)) ∧
  (∀ γ ν, Persistent (srvNet (GF := GF) γ ν)) ∧
  (∀ s γi, Persistent (srvIdSpace (GF := GF) s γi)) ∧
  (∀ s γ k, Persistent (srvReadAt (GF := GF) s γ k)) ∧
  (∀ s γ id, Persistent (srvNode (GF := GF) s γ id)) ∧
  (∀ s γ id, Persistent (srvStarted (GF := GF) s γ id)) ∧
  (∀ err, Persistent (httpForbidden (GF := GF) err)) ∧
  (∀ s γ k, Persistent (srvApplied (GF := GF) s γ k)) ∧
  (∀ r γ id n, Persistent (isRaftNode (GF := GF) r γ id n)) ∧
  (∀ rh s γ, Persistent (readyHandlerOk (GF := GF) rh s γ)) ∧
  (∀ r k, Persistent (nodeAdvanced (GF := GF) r k)) ∧
  (∀ r k, Persistent (nodeSnapLb (GF := GF) r k)) ∧
  (∀ r ch, Persistent (rnApplyc (GF := GF) r ch)) ∧
  (∀ r ch, Persistent (rnReadStateC (GF := GF) r ch)) ∧
  (∀ p k e, Persistent (entryAt (GF := GF) p k e)) ∧
  (∀ r rac k, Persistent (advancedAt (GF := GF) r rac k)) ∧
  (∀ sl ids, Persistent (expiredLeases (GF := GF) sl ids))

def timeless.spec : Prop :=
  (∀ γ k σ, Timeless (histAt (GF := GF) γ k σ)) ∧
  (∀ γ k id res, Timeless (answered (GF := GF) γ k id res)) ∧
  (∀ s γ k, Timeless (srvApplied (GF := GF) s γ k))

def exclusive.spec : Prop :=
  (∀ s γ ep p p', applyThread (GF := GF) s γ ep p ∗ applyThread s γ ep p' ⊢ iprop(False)) ∧
  (∀ r, rnLoop (GF := GF) r ∗ rnLoop r ⊢ iprop(False)) ∧
  (∀ r, rnStopper (GF := GF) r ∗ rnStopper r ⊢ iprop(False)) ∧
  (∀ s γ id ds, srvRunTok (GF := GF) s γ id ds ∗ srvRunTok s γ id ds ⊢ iprop(False)) ∧
  (∀ r k k', applycPos (GF := GF) r k ∗ applycPos r k' ⊢ iprop(False))

/-! ### The history (K6, K7: what the cluster's invariant keeps) -/

def histAt_agree.spec : Prop :=
  ∀ γ k (σ σ' : EtcdModel.State), histAt (GF := GF) γ k σ ∗ histAt γ k σ' ⊢ iprop(⌜σ = σ'⌝)

/-- A state of the history is one the cluster has been in (W0's `etcdLb`). -/
def histAt_lb.spec : Prop :=
  ∀ γ k (σ : EtcdModel.State), histAt (GF := GF) γ k σ ⊢ EtcdModel.etcdLb γ.etcd σ

/-- The history is the committed log's: only committed points have a state. -/
def histAt_committed.spec : Prop :=
  ∀ γ k (σ : EtcdModel.State), histAt (GF := GF) γ k σ ⊢
    ∃ l, Raft.committedLb γ.raft l ∗ ⌜k ≤ l.length⌝

/-- Every committed point has a state (the cluster's invariant, opened under `etcdN`). -/
def histAt_of_committed.spec : Prop :=
  ∀ (γ : Names) (l : List Raft.LogEntry) (E : CoPset), ↑EtcdModel.etcdN ⊆ E →
    Raft.committedLb (GF := GF) γ.raft l ⊢ |={E}=> ∃ σ, histAt γ l.length σ

/-- An answer is the answer of its entry (one per index). -/
def answered_agree.spec : Prop :=
  ∀ γ k (id id' : w64) (res res' : EtcdModel.Resp),
    answered (GF := GF) γ k id res ∗ answered γ k id' res' ⊢ iprop(⌜id = id' ∧ res = res'⌝)

/-- **Only etcd's own entries are committed**: normal entries and legacy conf changes (etcd proposes
no `ConfChangeV2`, so raft never enters a joint configuration and appends no empty
`EntryConfChangeV2`: R1's `committedLb_emptyV2`). The cluster's invariant: every proposal update it
fires is one of etcd's (2c's `processInternalRaftRequestOnce`, `configure`). -/
def committed_types.spec : Prop :=
  ∀ (γ : Names) (l : List Raft.LogEntry) (E : CoPset), ↑EtcdModel.etcdN ⊆ E →
    Raft.committedLb (GF := GF) γ.raft l ⊢
      |={E}=> ⌜∀ e ∈ l, e.type = Raft.EntryNormal ∨ e.type = Raft.EntryConfChange⌝

/-- (3a's) The apply's step is a step of the model (a client's `Step`, an environment step, or none):
the history is one `Reach` sequence (W0's `etcdLb_reach`, `etcdLb_ord`). -/
def applyStep_reach.spec : Prop :=
  ∀ mc σ e (σ' : EtcdModel.State) (res : EtcdModel.Resp),
    applyStep mc σ e σ' res → EtcdModel.Reach σ σ'

/-- (3a's) The apply is deterministic. -/
def applyStep_fun.spec : Prop :=
  ∀ mc σ e (σ1 σ2 : EtcdModel.State) (r1 r2 : EtcdModel.Resp),
    applyStep mc σ e σ1 r1 → applyStep mc σ e σ2 r2 → σ1 = σ2 ∧ r1 = r2

/-- **Proposing through the history** (2c's `processInternalRaftRequestOnce` and `configure`; the
cluster's invariant): a proposer turns its update over `etcdState` (fired with the apply's step of the
entry under the shared configuration `γ.mc`, the entry's bytes satisfying `D`) into raft's proposal
update (R1's `node.Propose.spec`, `node.ProposeConfChange.spec` form): at the entry's commit at index
`k`, the history's next point is `histAt γ k σ'` and the proposer's update fires there. Raft's
namespace is the cluster's `etcdN .@ "raft"` (2e's allocation; round 1, S1), and a normal entry has
data (an empty one is raft's own filler, S2). -/
def histPropose.spec : Prop :=
  ∀ (γ : Names) (ty : w32) (D : List w8 → Prop) (E : CoPset),
    ↑EtcdModel.etcdN ⊆ E → γ.raft.ns = EtcdModel.etcdN .@ "raft" →
    (∀ bs, D bs → ty = Raft.EntryNormal → bs ≠ []) →
    (AU <{ ∃∃ σ, EtcdModel.etcdState (GF := GF) γ.etcd σ }> @ ⊤ \ ↑EtcdModel.etcdN, ∅
      <{ ∀∀ (t : w64) (bs : List w8) (σ' : EtcdModel.State) (res : EtcdModel.Resp),
          ⌜D bs ∧ applyStep γ.mc σ ⟨t, ty, bs⟩ σ' res⌝ ∗ EtcdModel.etcdState γ.etcd σ', COMM True }>)
    ⊢ |={E}=> AU <{ ∃∃ (ops : List Raft.LogEntry), Raft.committedOps γ.raft ops }>
        @ ⊤ \ ↑γ.raft.ns, ∅
      <{ ∀∀ (t : w64) (bs : List w8), ⌜D bs⌝ ∗ Raft.committedOps γ.raft (ops ++ Raft.opsOf [⟨t, ty, bs⟩]),
         COMM True }>

/-- **Register a read context with raft** (2c's `readEnv` registration; round 1, completeness F2):
the cluster's invariant holds raft's `readCtxs`; a fresh request id of a started member's id space
gives a fresh context `be64 id`, registered with the update that certifies the committed log `l`. -/
def readCtx_register.spec : Prop :=
  ∀ (s : Loc) (γ : Names) (id : Nat) (γi : IdUtil.IdSpace) (rid : w64) (l : List Raft.LogEntry)
    (E : CoPset), ↑EtcdModel.etcdN ⊆ E →
    srvStarted (GF := GF) s γ id ∗ srvIdSpace s γi ∗ IdUtil.idFresh γi rid ∗ Raft.committedLb γ.raft l
      ⊢ |={E}=> Raft.readCtx γ.raft (Read.be64 rid) (Read.readLbQ l)

/-- **The read registry: register** (2c's `readReg_register`): a persistent update over `etcdState`
by `Rel` is registered at the current committed log `l0`. -/
def readReg_register.spec : Prop :=
  ∀ (γ : Names) (Rel : EtcdModel.State → EtcdModel.Resp → Prop)
    (Q : EtcdModel.State → EtcdModel.Resp → IProp GF) (E : CoPset), ↑EtcdModel.etcdN ⊆ E →
    □ (AU <{ ∃∃ σ, EtcdModel.etcdState (GF := GF) γ.etcd σ }> @ ⊤ \ ↑EtcdModel.etcdN, ∅
        <{ ∀∀ (res : EtcdModel.Resp), ⌜Rel σ res⌝ ∗ EtcdModel.etcdState γ.etcd σ, COMM Q σ res }>)
      ⊢ |={E}=> ∃ t l0, readTicket γ t Rel Q l0 ∗ Raft.committedLb γ.raft l0

/-- **The read registry: get** (2c's `readReg_get`): at a history point at or past the registration
(its committed log extending `l0`'s operations), the update's result for an answer `Rel` allows. -/
def readReg_get.spec : Prop :=
  ∀ (γ : Names) t Rel (Q : EtcdModel.State → EtcdModel.Resp → IProp GF) (l0 l : List Raft.LogEntry)
    (k : Nat) (σ : EtcdModel.State) (res : EtcdModel.Resp) (E : CoPset),
    ↑EtcdModel.etcdN ⊆ E → Raft.opsOf l0 <+: Raft.opsOf l → l.length ≤ k → Rel σ res →
    readTicket (GF := GF) γ t Rel Q l0 ∗ Raft.committedLb γ.raft l ∗ histAt γ k σ ⊢ |={E}=> Q σ res

/-- **2e's handle names a member of the history** (2c's item 1): a started server of W0's cluster
`γ` is a member of some server-level names over it. -/
def isServer_names.spec : Prop :=
  ∀ (s : Loc) (γ : EtcdModel.Cluster), isServer (GF := GF) s γ ⊢
    ∃ (N : Names) (id : Nat), ⌜N.etcd = γ⌝ ∗ srvNode s N id ∗ srvStarted s N id ∗
      (∃ γi, srvIdSpace s γi)

/-- **2e's built member is a member of the history** (round 1, completeness F4): `NewServer`'s
persistent `srvMember` gives `srvNode` at the names over its cluster. -/
def srvMember_node.spec : Prop :=
  ∀ (s : Loc) (γ : EtcdModel.Cluster) (id : Nat), srvMember (GF := GF) s γ id ⊢
    ∃ N : Names, ⌜N.etcd = γ⌝ ∗ srvNode s N id

/-- One server, one member of one names. -/
def srvNode_agree.spec : Prop :=
  ∀ s (γ γ' : Names) (id id' : Nat), srvNode (GF := GF) s γ id ∗ srvNode s γ' id' ⊢
    iprop(⌜γ = γ' ∧ id = id'⌝)

/-- **`run`'s token from what `start` holds** (round 1, completeness F4): the driver placed at
`s.r` with its loop, stopper and `applyc` cursor at the start's delivered length, the location-free
initial apply state, 2e's closers for `ds` (`Cleanup`'s), the right to receive on `s.stop`, and the
escrow of `s.done`'s close (2e's `srvRunning` reads it). -/
def srvRunTok_intro.spec : Prop :=
  ∀ (s : Loc) (γ : Names) (id : Nat) (ds : Config.Dirs) (n : Loc) (p : Progress) (c : Nat),
    srvNode (GF := GF) s γ id ∗ srvStarted s γ id ∗
    isRaftNode (structFieldRef go_etcd_io.etcd.server.v3.etcdserver.EtcdServer go!"r" s) γ (W64 id) n ∗
    rnLoop (structFieldRef go_etcd_io.etcd.server.v3.etcdserver.EtcdServer go!"r" s) ∗
    rnStopper (structFieldRef go_etcd_io.etcd.server.v3.etcdserver.EtcdServer go!"r" s) ∗
    applycPos (structFieldRef go_etcd_io.etcd.server.v3.etcdserver.EtcdServer go!"r" s)
      (uint.nat p.appliedi) ∗
    applyInit s γ p c ∗ ⌜uint.nat p.appliedi ≤ c⌝ ∗ srvClosers s ds ⊢ srvRunTok s γ id ds

/-- **`run` allocates `ep`**: the initial state with its record is the apply thread's. -/
def applyInit_ep.spec : Prop :=
  ∀ s γ (p : Progress) (c : Nat) (ep : Loc) (cs : Loc),
    applyInit (GF := GF) s γ p c ∗
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.etcdProgress go!"appliedi" ep ↦ p.appliedi ∗
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.etcdProgress go!"appliedt" ep ↦ p.appliedt ∗
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.etcdProgress go!"diskSnapshotIndex" ep ↦ p.diskSnap ∗
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.etcdProgress go!"memorySnapshotIndex" ep ↦ p.memSnap ∗
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.etcdProgress go!"confState" ep ↦ cs
      ⊢ |==> applyThread s γ ep p

/-- **A stopped member's directories** (round 1, completeness F4): what `run`'s shutdown leaves and
what 2e's `Cleanup` gives back make the member's durable state, which a restart takes. -/
def srvStopped_disk.spec : Prop :=
  ∀ s (γ : Names) (id : Nat) (ds : Config.Dirs),
    srvStopped (GF := GF) s γ id ds ∗ srvClosed ds ⊢ memberDisk γ.etcd id ds

/-- **The applied point bounds the member's reads** (round 1, completeness F1; the slot's
introduction). -/
def srvApplied_read.spec : Prop :=
  ∀ s γ (id k : Nat), srvNode (GF := GF) s γ id ∗ srvApplied s γ k ⊢ srvReadAt s γ k

/-- `s.errorc` is 2f's error channel (any goroutine may send without blocking; `run` stops on it). -/
def srvNode_errorc.spec : Prop :=
  ∀ s γ id, srvNode (GF := GF) s γ id ⊢
    ∃ ch : Loc, structFieldRef go_etcd_io.etcd.server.v3.etcdserver.EtcdServer go!"errorc" s ↦□ ch ∗
      Rafthttp.errChanOk ch

/-- **A snapshot's point** (round 1, F3/F4): its image's history point, at or past its index, with
the snapshot's configuration; both the `Ready` loop (to name the node's configuration point at
`Advance`, R1's wand) and the apply thread (whose state machine the image is) read it. -/
def snapImage_point.spec : Prop :=
  ∀ γ (s : Raft.Snapshot), snapImage (GF := GF) γ s ⊢
    ∃ (a : Nat) (m : Raft.Membership) (σ : EtcdModel.State), snapPoint γ s a ∗ histAt γ a σ ∗
      Raft.confAt γ.raft a m ∗ ⌜uint.nat s.index ≤ a ∧ s.conf.Is m⌝

/-- A snapshot has one point. -/
def snapPoint_agree.spec : Prop :=
  ∀ γ (s : Raft.Snapshot) (a a' : Nat), snapPoint (GF := GF) γ s a ∗ snapPoint γ s a' ⊢ iprop(⌜a = a'⌝)

/-! ### A member -/

def srvApplied_mono.spec : Prop :=
  ∀ s γ (k k' : Nat), k' ≤ k → srvApplied (GF := GF) s γ k ⊢ srvApplied s γ k'

def srvReadAt_mono.spec : Prop :=
  ∀ s γ (k k' : Nat), k' ≤ k → srvReadAt (GF := GF) s γ k ⊢ srvReadAt s γ k'

def srvApplied_zero.spec : Prop := ∀ s γ, ⊢ srvApplied (GF := GF) s γ 0

/-- An applied point is a committed one. -/
def srvApplied_hist.spec : Prop :=
  ∀ s γ (k : Nat), srvApplied (GF := GF) s γ k ⊢ ∃ σ, histAt γ k σ

/-- The server's raft node driver is at `s.r`. -/
def srvNode_raftNode.spec : Prop :=
  ∀ s γ id, srvNode (GF := GF) s γ id ⊢
    ∃ n, isRaftNode (structFieldRef go_etcd_io.etcd.server.v3.etcdserver.EtcdServer go!"r" s) γ
      (W64 id) n

/-- **`Process`'s refusals are `Process` errors** (2f's `procErr`: their `Error()` and `WriteTo`
meet the transport's handlers' needs). -/
def procErr_forbidden.spec : Prop :=
  ∀ (err : GoInterface), httpForbidden (GF := GF) err ⊢ Rafthttp.procErr err

/-- The driver's node is a node of the raft cluster. -/
def isRaftNode_node.spec : Prop :=
  ∀ r γ id n, isRaftNode (GF := GF) r γ id n ⊢ Raft.isNode n γ.raft id

/-- **Placing a fresh driver** (`NewServer`'s `r: *newRaftNode(...)`, a copy of the value into the
server's field): the driver at its new address, with its loop, its stopper. -/
def rnInit_place.spec : Prop :=
  ∀ (a : Loc) (v : go_etcd_io.etcd.server.v3.etcdserver.raftNode) γ id n,
    rnInit (GF := GF) v γ id n ∗ a ↦ v ⊢ |==> isRaftNode a γ id n ∗ rnLoop a ∗ rnStopper a

/-- **The driver's storage** (round 1, F7): its `MemoryStorage` is the node's attached storage. -/
def isRaftNode_storage.spec : Prop :=
  ∀ r γ id n, isRaftNode (GF := GF) r γ id n ⊢
    ∃ ms : Loc,
      structFieldRef go_etcd_io.etcd.server.v3.etcdserver.raftNodeConfig go!"raftStorage"
        (structFieldRef go_etcd_io.etcd.server.v3.etcdserver.raftNode go!"raftNodeConfig" r) ↦□ ms ∗
      Raft.nodeStorage n γ.raft (Raft.memStor ms)

/-- `nodeSnapLb` and `nodeAdvanced` are R1's facts of the driver's node. -/
def nodeSnapLb_stor.spec : Prop :=
  ∀ r γ id n k, isRaftNode (GF := GF) r γ id n ∗ nodeSnapLb r k ⊢ Raft.storSnapLb n k

def nodeAdvanced_applied.spec : Prop :=
  ∀ r γ id n k, isRaftNode (GF := GF) r γ id n ∗ nodeAdvanced r k ⊢ Raft.appliedLb n k

/-- **The `msgSnapC` receive** (`applyAll`'s `select`; round 1, F7): a `MsgSnap` the node sent,
with a non-zero term (R1's, requested). -/
def msgSnapC_recv.spec : Prop :=
  ∀ (r : Loc) γ id n (Φ : Loc → Bool → IProp GF),
    isRaftNode (GF := GF) r γ id n ⊢
      ∃ (ch : Loc) (γc : ChanNames), structFieldRef go_etcd_io.etcd.server.v3.etcdserver.raftNode go!"msgSnapC" r ↦□ ch ∗ isChan ch γc Loc ∗
        (£ 1 ∗ £ 1 -∗ (▷ ∀ mp, (∃ (m : Raft.Msg) (sn : Raft.Snapshot),
            Raft.msgPts mp (DFrac.own 1) m ∗ Raft.msgSent γ.raft m ∗
            ⌜m.type = Raft.MsgSnap ∧ m.src = id ∧ m.snapshot = some sn ∧ m.term ≠ W64 0⌝) -∗
            Φ mp true) -∗
          recvAu γc Loc Φ)

/-- (R1's term bound, requested; round 1, F5) **A batch's terms**: every committed entry and the
snapshot of a batch have terms at most its `raftTerm` when that is non-zero, and the apply thread's
applied term is at most it then too. -/
def applyBatch_terms.spec : Prop :=
  ∀ r γ apv (B : ApplyBatch) ph s ep (p : Progress),
    applyBatch (GF := GF) r γ apv B ph ∗ applyThread s γ ep p ⊢
      applyBatch r γ apv B ph ∗ applyThread s γ ep p ∗
      ⌜B.term ≠ W64 0 → uint.nat p.appliedt ≤ uint.nat B.term ∧
        (∀ e ∈ B.ents, uint.nat e.term ≤ uint.nat B.term) ∧
        (∀ sn, B.snap = some sn → uint.nat sn.term ≤ uint.nat B.term)⌝

/-- The apply thread is `applyAt` at its recorded progress. -/
def applyThread_at.spec : Prop :=
  ∀ s γ ep (p : Progress),
    applyThread (GF := GF) s γ ep p ⊣⊢ ∃ c ai, applyAt s γ ep p (uint.nat p.appliedi) c ai

/-- **The applyc receive** (in `run`'s `select`): the next batch, in order (round 1, F2: the
cursor `applycPos` moves from the batch's `prev` to its `last`). -/
def applyc_recv.spec : Prop :=
  ∀ (r ch : Loc) γ id n (k : Nat) (Φ : go_etcd_io.etcd.server.v3.etcdserver.toApply → Bool → IProp GF),
    rnApplyc (GF := GF) r ch ∗ isRaftNode r γ id n ⊢
      ∃ (_ : Pos.Countable go_etcd_io.etcd.server.v3.etcdserver.toApply) (γc : ChanNames),
        isChan ch γc go_etcd_io.etcd.server.v3.etcdserver.toApply ∗
        (£ 1 ∗ £ 1 -∗ applycPos r k -∗
          (▷ ∀ apv, (∃ B, applyBatch r γ apv B false ∗ ⌜B.prev = k⌝ ∗ applycPos r B.last) -∗
            Φ apv true) -∗
          recvAu γc go_etcd_io.etcd.server.v3.etcdserver.toApply Φ)

/-- **The readStateC receive** (the read loop's, 2c): a read state of the cluster (R1's `readState`)
with its context. -/
def readStateC_recv.spec : Prop :=
  ∀ (r ch : Loc) γ id n (Φ : go_etcd_io.raft.v3.ReadState → Bool → IProp GF),
    rnReadStateC (GF := GF) r ch ∗ isRaftNode r γ id n ⊢
      ∃ (_ : Pos.Countable go_etcd_io.raft.v3.ReadState) (γc : ChanNames),
        isChan ch γc go_etcd_io.raft.v3.ReadState ∗
        (£ 1 ∗ £ 1 -∗ (▷ ∀ rs, (∃ c, rs.RequestCtx' ↦*□ c ∗
            Raft.readState γ.raft c rs.Index') -∗ Φ rs true) -∗
          recvAu γc go_etcd_io.raft.v3.ReadState Φ)

/-- The apply thread's applied index is applied. -/
def applyThread_applied.spec : Prop :=
  ∀ s γ ep (p : Progress), applyThread (GF := GF) s γ ep p ⊢
    applyThread s γ ep p ∗ srvApplied s γ (uint.nat p.appliedi)

end laws

end EtcdServer
end EtcdGrove
end Perennial
