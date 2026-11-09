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
entry, a conf change, a lease checkpoint, a cluster version). The answer the commit fixed for a
request is `answered γ k id res` (persistent). So **the history is the committed log's** (K6): a
snapshot, a restore and a restart continue the same `histAt`; the member's own position in it is
its applied index.

**A member.** `isServer s γ id` (persistent): `s` is member `id`'s `*EtcdServer` (its fields after
`start`, their invariants). `srvApplied s γ k` (persistent): the member has applied the committed
log's first `k` entries, so its KV store (and lessor, auth store, membership) is at least at
`histAt γ k` (2c's linearizable reads wait for it: `applyWait`). `srvRunTok s γ id` (exclusive):
what `start` hands `run` (2e builds it at `NewServer`/`start`). `srvStopped s γ id` (exclusive):
what a stopped member leaves (`run`'s `close(done)` announces it): the durable halves a restart
takes (the WAL's `raftState`, the backend's image, raft's `nodeVacant`), which 2e's restart consumes.

**The apply thread.** `applyThread s γ ep p` (exclusive): the apply thread's state, with the
`etcdProgress` record `ep` at `p : Progress` (applied index and term, the disk and memory snapshot
indices): the state machine (the uber-applier over mvcc, the lessor, auth, membership, alarms, the
consistent indexer) at `histAt γ k` for `k = max p.appliedi ci` (the backend may be ahead of the
applied index after a restart: entries up to the consistent index `ci` are replayed for the
in-memory membership only, `shouldApplyV3 = false`), the node's configuration view (R1's
`nodeConf`) at the same point, and `ep.confState` listing it. Passed from one `applyAll` job to the
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

* `Names`: `etcd`, `raft`, `cfg` and the names of the history (a `mono_list` of states, one per
  committed index: `histAt` its fragments, with the authority in the cluster's invariant together
  with `committedOps γ.raft ops`, `⌜|hist| = |committed log|⌝`, the answers (`answered`, a persistent
  map from index to `(id, res)`), the cluster's half of `etcdState γ.etcd (last hist)`, raft's
  `confDecisions`/`snapsMade`/`readCtxs`, each made snapshot's database image (`snapImage`)).
* `isServer s γ id`: the server's read-only fields (`s.r`, `s.w`, `s.applyWait`, `s.consistIndex`,
  `s.cluster`, `s.kv`, `s.lessor`, `s.authStore`, `s.alarmStore`, `s.beHooks`, `s.snapshotter`,
  `s.Cfg`, the channels) as persistent points-to's, the invariants of the atomics (`appliedIndex`
  with `srvApplied` of its value, `committedIndex` with a committed prefix at least that long,
  `term`, `lead`: any value), the `bemu` lock's invariant (the current backend, whose state machine
  is the apply thread's), `inflightSnapshots`, `envUpd γ.etcd γ.cfg` (persistent), and the cluster's
  invariant.
* `applyThread`: the `etcdProgress` points-to's, `Cindex.ciWriter`, the uber-applier's contract
  (3a's) at the server's state machine, R1's `nodeConf`, `confAt γ.raft k m` with `ep.confState`
  listing `m`, the snapshot indices with `storSnapLb`, `Schedule`'s job chain position.
* `isRaftNode`/`rnLoop`/`rnStopper`/`applyBatch`: the loop's ghost driver state (R1's `nodeDriver`,
  `readyStor`), the `applyc` protocol (each batch's committed entries with `committedLb`/
  `deliveredLb`, its snapshot's `snapValid`, the `notifyc` handshake: the loop's `Save` before the
  apply thread's snapshot (the WAL's synced write), the apply thread's conf changes before the loop's
  `Advance`; `raftAdvancedC`'s close carrying R1's `appliedLb n` of the delivered log), `msgSnapC`'s
  payload (a `MsgSnap` the node sent: `msgPts`, `msgSent`), `readStateC`'s (`readState`).

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

/-- **An etcd cluster's server-level names**: the client-observable cluster (W0's names), the raft
cluster under it (R1's names), the environment's configuration (every member configured alike, the
cluster contract), and the history's own names. -/
structure Names where
  etcd : EtcdModel.Cluster
  raft : Raft.Cluster
  cfg : EtcdModel.EnvCfg
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

/-- The delivered log's length after the batch. -/
def ApplyBatch.last (B : ApplyBatch) : Nat :=
  match B.snap with
  | some s => uint.nat s.index
  | none => B.prev + B.ents.length

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

/-- **The database image of raft snapshot `s`** (its `.snap.db`, a backend file) holds the state
machine at `histAt γ s.index`: what a member's merged snapshot sends (`createMergedSnapshotMessage`)
and what a member installing it opens (`applySnapshot`). Persistent. -/
opaque snapImage (γ : Names) (s : Raft.Snapshot) : IProp GF := iprop(True)

/-! ### A member -/

/-- **`s` is member `id`'s server in cluster `γ`** (after `start`). Persistent. -/
opaque isServer (s : Loc) (γ : Names) (id : w64) : IProp GF := iprop(True)

/-- **Member `s` has applied the committed log's first `k` entries.** Persistent. -/
opaque srvApplied (s : Loc) (γ : Names) (k : Nat) : IProp GF := iprop(True)

/-- **What `start` hands `run`** (2e builds it). Exclusive. -/
opaque srvRunTok (s : Loc) (γ : Names) (id : w64) : IProp GF := iprop(True)

/-- **What a stopped member leaves** (`run`'s `close(done)`): the durable halves a restart takes.
Exclusive. -/
opaque srvStopped (s : Loc) (γ : Names) (id : w64) : IProp GF := iprop(True)

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

/-- **A `raftNode` value fresh from `newRaftNode`**, for member `id` over node `n`: its channels new,
its node, storages and transport the configuration's, with their resources. Exclusive. -/
opaque rnInit (v : go_etcd_io.etcd.server.v3.etcdserver.raftNode) (γ : Names) (id : w64) (n : Loc) :
    IProp GF := iprop(True)

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

/-- `ch` is driver `r`'s `applyc`. Persistent. -/
opaque rnApplyc (r : Loc) (ch : Loc) : IProp GF := iprop(True)

/-- `ch` is driver `r`'s `readStateC`. Persistent. -/
opaque rnReadStateC (r : Loc) (ch : Loc) : IProp GF := iprop(True)

/-! ### Values exchanged with other packages (provisional: their batches' vocabulary) -/

/-- (provisional, raftpb's, 3h) **`p` points to a committed entry `e`**, read-only for good (an
element of R1's `entriesRO`). Persistent. -/
opaque entryAt (p : Loc) (e : Raft.LogEntry) : IProp GF := iprop(True)

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
  (∀ s γ id, Persistent (isServer (GF := GF) s γ id)) ∧
  (∀ s γ k, Persistent (srvApplied (GF := GF) s γ k)) ∧
  (∀ r γ id n, Persistent (isRaftNode (GF := GF) r γ id n)) ∧
  (∀ rh s γ, Persistent (readyHandlerOk (GF := GF) rh s γ)) ∧
  (∀ r k, Persistent (nodeAdvanced (GF := GF) r k)) ∧
  (∀ r k, Persistent (nodeSnapLb (GF := GF) r k)) ∧
  (∀ r ch, Persistent (rnApplyc (GF := GF) r ch)) ∧
  (∀ r ch, Persistent (rnReadStateC (GF := GF) r ch)) ∧
  (∀ p e, Persistent (entryAt (GF := GF) p e)) ∧
  (∀ sl ids, Persistent (expiredLeases (GF := GF) sl ids))

def timeless.spec : Prop :=
  (∀ γ k σ, Timeless (histAt (GF := GF) γ k σ)) ∧
  (∀ γ k id res, Timeless (answered (GF := GF) γ k id res)) ∧
  (∀ s γ k, Timeless (srvApplied (GF := GF) s γ k))

def exclusive.spec : Prop :=
  (∀ s γ ep p p', applyThread (GF := GF) s γ ep p ∗ applyThread s γ ep p' ⊢ iprop(False)) ∧
  (∀ r, rnLoop (GF := GF) r ∗ rnLoop r ⊢ iprop(False)) ∧
  (∀ r, rnStopper (GF := GF) r ∗ rnStopper r ⊢ iprop(False)) ∧
  (∀ s γ id, srvRunTok (GF := GF) s γ id ∗ srvRunTok s γ id ⊢ iprop(False))

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
  ∀ γ (l : List Raft.LogEntry) (E : CoPset), ↑EtcdModel.etcdN ⊆ E →
    Raft.committedLb (GF := GF) γ.raft l ⊢ |={E}=> ∃ σ, histAt γ l.length σ

/-- An answer is the answer of its entry (one per index). -/
def answered_agree.spec : Prop :=
  ∀ γ k (id id' : w64) (res res' : EtcdModel.Resp),
    answered (GF := GF) γ k id res ∗ answered γ k id' res' ⊢ iprop(⌜id = id' ∧ res = res'⌝)

/-- A snapshot's image is at a committed point (its index has a state). -/
def snapImage_hist.spec : Prop :=
  ∀ γ (s : Raft.Snapshot), snapImage (GF := GF) γ s ⊢ ∃ σ, histAt γ (uint.nat s.index) σ

/-! ### A member -/

def srvApplied_mono.spec : Prop :=
  ∀ s γ (k k' : Nat), k' ≤ k → srvApplied (GF := GF) s γ k ⊢ srvApplied s γ k'

def srvApplied_zero.spec : Prop := ∀ s γ, ⊢ srvApplied (GF := GF) s γ 0

/-- An applied point is a committed one. -/
def srvApplied_hist.spec : Prop :=
  ∀ s γ (k : Nat), srvApplied (GF := GF) s γ k ⊢ ∃ σ, histAt γ k σ

/-- The server's raft node driver is at `s.r`. -/
def isServer_raftNode.spec : Prop :=
  ∀ s γ id, isServer (GF := GF) s γ id ⊢
    ∃ n, isRaftNode (structFieldRef go_etcd_io.etcd.server.v3.etcdserver.EtcdServer go!"r" s) γ id n

/-- The driver's node is a node of the raft cluster. -/
def isRaftNode_node.spec : Prop :=
  ∀ r γ id n, isRaftNode (GF := GF) r γ id n ⊢ Raft.isNode n γ.raft id

/-- **Placing a fresh driver** (`NewServer`'s `r: *newRaftNode(...)`, a copy of the value into the
server's field): the driver at its new address, with its loop, its stopper. -/
def rnInit_place.spec : Prop :=
  ∀ (a : Loc) (v : go_etcd_io.etcd.server.v3.etcdserver.raftNode) γ id n,
    rnInit (GF := GF) v γ id n ∗ a ↦ v ⊢ |==> isRaftNode a γ id n ∗ rnLoop a ∗ rnStopper a

/-- The apply thread is `applyAt` at its recorded progress. -/
def applyThread_at.spec : Prop :=
  ∀ s γ ep (p : Progress),
    applyThread (GF := GF) s γ ep p ⊣⊢ ∃ c ai, applyAt s γ ep p (uint.nat p.appliedi) c ai

/-- **The applyc receive** (in `run`'s `select`): a batch, in order. -/
def applyc_recv.spec : Prop :=
  ∀ (r ch : Loc) γ id n (Φ : go_etcd_io.etcd.server.v3.etcdserver.toApply → Bool → IProp GF),
    rnApplyc (GF := GF) r ch ∗ isRaftNode r γ id n ⊢
      ∃ (_ : Pos.Countable go_etcd_io.etcd.server.v3.etcdserver.toApply) (γc : ChanNames),
        isChan ch γc go_etcd_io.etcd.server.v3.etcdserver.toApply ∗
        (£ 1 ∗ £ 1 -∗ (▷ ∀ apv, (∃ B, applyBatch r γ apv B false) -∗ Φ apv true) -∗
          recvAu γc go_etcd_io.etcd.server.v3.etcdserver.toApply Φ)

/-- **The readStateC receive** (the read loop's, 2c): a read state of the cluster (R1's `readState`)
with its context. -/
def readStateC_recv.spec : Prop :=
  ∀ (r ch : Loc) γ id n (Φ : go_etcd_io.raft.v3.ReadState → Bool → IProp GF),
    rnReadStateC (GF := GF) r ch ∗ isRaftNode r γ id n ⊢
      ∃ (_ : Pos.Countable go_etcd_io.raft.v3.ReadState) (γc : ChanNames),
        isChan ch γc go_etcd_io.raft.v3.ReadState ∗
        (£ 1 ∗ £ 1 -∗ (▷ ∀ rs, (∃ c, ownSlice rs.RequestCtx' c DFrac.discard ∗
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
