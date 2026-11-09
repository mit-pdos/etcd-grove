/-
# Raft's node API (batch R1): the vocabulary

What a client of raft (etcd's server, rafthttp, this repository's examples) may use of raft:
the pure model is `Model.lean` (transparent); this module has the resources (opaque) and their
laws (obligations, `def <law>.spec : Prop`). The specs of the functions are the files beside it
(`StartNode.lean`, `node__Propose.lean`, `MemoryStorage__Append.lean`, ...).

## The shape, in words

A **cluster** `γ : Cluster` (raft group) is allocated by the client (`cluster_alloc`), with its
initial configuration, its bootstrap log (`StartNode`'s, or none), its namespace `γ.ns` (raft's
invariants; the client's atomic updates are fired at `⊤ ∖ ↑γ.ns`) and its credit mode `γ.dup`.

**The committed log, the client's linearization.** The client owns `committedOps γ ops` (the
operations committed so far: the committed log without raft's own entries, `opsOf`); raft moves it
when an entry commits, by firing the update the client handed to `Propose`/`ProposeConfChange`.
Anyone may hold `committedLb γ l` (the committed log, from index 1, extends `l`). A linearizable read
registers a persistent update under a fresh context (`readCtx`), passes the context to `ReadIndex`,
and gets `readState γ c i` back in a `Ready`: the update fired when the committed log was `i` long.

**Configurations.** `confAt γ k m`: the configuration after the first `k` committed entries is `m`,
the same at every node. The client decides each committed conf-change entry once for the cluster
(`confDecisions`, `confDecided`: apply a change, or skip), and each node's tracker follows its
`nodeConf n γ v`, which `ApplyConfChange` moves.

**Snapshots** are the client's: `snapsMade γ S` is the set of snapshots made (with their data, of
which the client keeps whatever invariant it wants), `snapValid γ s` says `s` was made, at a committed
prefix, with that prefix's configuration. `CreateSnapshot` stores only valid snapshots; raft hands out
only valid ones (`Ready.Snapshot`, `MsgSnap`).

**Messages** are values (`Msg`): `msgSent γ m` (persistent) says a node of `γ` sent `m`; the
proposals a `MsgProp` carries are its `msgCredit γ m` (exclusive, unless `γ.dup`: then persistent).
A transport carries both with the bytes; `Step` takes them.

**Nodes and durability** (the user-approved design, `.claude/skills/spec/examples/
raft-durable-node-api.md`). The client owns `raftState γ id D` (node `id`'s durable state: term,
vote, log) and `nodeVacant γ id` (no node of `id` runs). A start takes both and returns the node `n`:
`isNode n γ id` (persistent), `nodeRunning n 1` (fractional; `Stop` takes it whole), the `Ready`
loop's `nodeDriver n γ st`, the configuration view `nodeConf n γ v`, and the storage's
`nodeStorage n S`. Each `Ready` hands out **an update to enter its batch** (`readyEnter`): fired when
the client makes the batch durable (or at once, for a client keeping nothing), it moves `raftState`
and gives the permission to send (`msgSent`), the read states and the driver back for `Advance`; and
**a persistent check** (`readyCheck`) giving a leader's messages before the write (etcd's
send-before-write). The volatile state stays in raft: a restart is a fresh volatile half over the
client's `raftState`, from a storage that holds it (`StorageHolds`).

**Storage.** A `Storage` is any implementation of raft's interface whose contents are presented as a
`StorState` through a client predicate `S` (`isStorage st S cf`: the interface's contract, a bundle as
`sync.isLocker` is); `MemoryStorage` meets it with `memStor ms`. At a start, raft takes `S σ` into its
invariant for good (a storage is attached once). The client then writes it only through updates raft
hands out: the batch's snapshot and entries (`readyStor`, from the `Ready`), a compaction up to the
applied index and the snapshot (`appliedLb`, `storSnapLb`), a snapshot at the applied index
(`stor_createSnapshot`), any hard state (`stor_setHardState`). A detached storage (before the start)
is the client's: its methods' updates fire on `memStor ms σ` directly.

## Intended realization (raft's proof)

- `Cluster`: the ghost names of raft's protocol (the old `RaftNames`/`Cluster`): the cluster-wide
  committed-log authority and its lower bounds (`committedLb` a fragment), the client's `committedOps`
  (the authority's client half: an `ownMap`/`mono_list` pair, opsOf-related to the authority by the
  commit invariant), the configuration map `k ↦ m` (persistent points-to's: `confAt`), the decision
  map (`confDecisions` the authority, `confDecided` the fragments), the snapshot set, the read-context
  registry (saved predicates of the read updates), the per-id durable state and vacancy tokens (ghost
  vars), the fresh-id authority; the proposals' and reads' updates are deposited in raft's invariant
  (`inv γ.ns`) when a node appends the entry or confirms the read.
- `msgSent`: the persistent record of messages sent (a ghost set of `Msg` with each one's protocol
  facts: the sender's term, log, votes, commit knowledge); `msgCredit`: the message's deposited
  proposal updates (a `£`-backed token per proposal, or their persistent copies when `γ.dup`).
- `isNode`, `nodeRunning`, `nodeDriver`, `nodeConf`, `deliveredLb`, `appliedLb`, `nodeStorage`,
  `storSnapLb`, `readyStor`, `isReadyChan`: the node's invariant over its channels and the
  `RawNode` it owns (the run goroutine holds the `RawNode`'s token), ghost vars for the driver
  state, the configuration view, mono-nat lower bounds for applied. The attached storage is the
  log's (R3, `ApiLog.lean`): `nodeStorage n γ S` is R3's `logStorage l S (snapValid γ) N` of the
  node's raft log `l` (the log's invariant, not the node's, holds `S σ` with the relation between `σ`
  and the log: stored entries the stable log, compaction point a floor and at most the stored
  snapshot's index, stored snapshot valid); `storSnapLb n j` is `j = 0` or R3's `logSnapLb l j`;
  `appliedLb n i` is `i = 0` or R3's `logFloor l i t` for the committed log's term `t` at `i` (R2's
  commit facts tie the floor's term to `committedLb`, as `stor_createSnapshot` needs; R2's
  `rawNodeAt_advance` publishes it with `raftLog_publish`); `readyStor n so k es` is R3's
  `logPending l h so.isSome (es ≠ [])` of the batch `h` handed out (`h.start = k`); the storage laws
  (`readyStor_*`, `stor_*`) are R3's `logStor_*` at mask `⊤` (at index `0`, a compaction is the
  identity, through `logStor_read`; an append of nothing likewise). (Integration I2: checked against
  R3's laws as they now are.) `rawNode`: the `RawNode`'s own token (the raft struct, the log, the
  tracker, the read-only queue: R2's, R3's and R4's predicates).
- `memStor ms σ`: a ghost var of `σ` whose authority is in `MemoryStorage`'s lock invariant,
  together with a fractional share of the footprint `InitialState` reads without the lock (the
  `snapshot` and `hardState` fields, the snapshot's `Metadata.ConfState` field and that `ConfState`,
  stored ensured: `AutoLeave` present); the lock invariant holds the other share and the `ents`
  slice. A writer opens its update once per store to that footprint (abort where the contents are
  unchanged, commit at the store that changes them). (Round 1, S1.) The `callStats` counters, which
  `InitialState` bumps unlocked, are wholly `memStor`'s (no locked method touches them; round 2).

## Requirement snippets

`examples/specreq/raftnode/`: `propose.go` (proposals, one-shot and retried), `readindex.go`
(linearizable reads), `readyloop.go` (the `Ready` loop with and without durability, leader
send-before-write, snapshots installed, conf changes applied before `Advance`), `confchange.go`
(v1 and v2 changes, refusal), `storage.go` (MemoryStorage before and after the start: bootstrap from
a WAL image, snapshot and compaction), `restart.go` (start, stop, restart from durable state),
`transport.go` (rafthttp: Step, ReportUnreachable, ReportSnapshot, the merged MsgSnap).
-/
module

public import Spec.go_etcd_io.raft.v3.Model
public import Spec.go_etcd_io.raft.v3.raftpb.Api
public import Spec.go_etcd_io.raft.v3.tracker.Api
public import Spec.PkgInit.go_etcd_io.raft.v3
public import Spec.context.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Raft

open Iris Iris.BI

/-! ## Ghost names -/

/-- A raft cluster's ghost names (opaque). -/
opaque Cluster : Type := Unit

/-- The namespace of the cluster's invariants (the client's choice at allocation). -/
opaque Cluster.ns : Cluster → Namespace

/-- Whether the proposals' credits are persistent (a transport that may deliver a message twice)
or one-shot (the client's choice at allocation; `msgCredit_dup`). -/
opaque Cluster.dup : Cluster → Bool

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
  {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
  [package_sem : go_etcd_io.raft.v3.Assumptions]

/-! ## raftpb's Go ownership

raftpb's predicates (batch 3h, `raftpb/Api.lean`), re-exported under the names this API used
while they were provisional (integration I2): `entriesRO sl k es` (a slice of read-only entries,
the first at index `k`), `msgPts p dq m` (a well-formed `*Message`), `hardStatePts`, `snapshotPts`
(a **full** `*Snapshot`: metadata, its `ConfState`, `Index`, `Term` and `AutoLeave` set, as raft's
and `MemoryStorage`'s are), `confStatePts` (a `*ConfState`, any presence), `confChangePts v dq c`
(a `ConfChangeI` interface value), `entryRO`, `entryPtrs`, and `msgRecv p m` (a **received**
message: `msgPts` at `own 1` with its `Entries` slice's capacity, which a stepped message must
have: integration I2). Their persistence, unfold and relation
laws are raftpb's (`RaftPb.raftpb_persistent`, `msgPts_unfold`, ...). -/

end vocab

export RaftPb (entriesRO msgPts msgRecv hardStatePts snapshotPts confStatePts confChangePts entryRO
  entryPtrs)

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
  {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
  [package_sem : go_etcd_io.raft.v3.Assumptions]

/-! ## raft's own Go structs -/

/-- A `Ready`'s `*SoftState`: `nil` for `none`, else read-only (leader, role). -/
opaque softStateOpt (p : Loc) (o : Option (w64 × w64)) : IProp GF := iprop(True)

/-- A `Ready`'s `ReadStates`, read-only: each `(RequestCtx, Index)`. -/
opaque readStatesRO (sl : GoSlice) (rs : List (List w8 × w64)) : IProp GF := iprop(True)

/-- A `[]Peer` slice (`dq` of it and of the contexts): ids and contexts. -/
opaque peersPts (sl : GoSlice) (dq : DFrac) (ps : List (w64 × List w8)) : IProp GF := iprop(True)

/-- A `Status` value's own memory (its `Progress` map and its configuration's maps, fresh copies:
`getStatus` clones them). -/
opaque statusOwn (s : go_etcd_io.raft.v3.Status) : IProp GF := iprop(True)

/-- A `*HardState` that may be `nil` (the empty hard state), read-only. -/
def hsPtr (p : Loc) (dq : DFrac) (hs : HardState) : IProp GF :=
  iprop(⌜p = null ∧ hs = HardState.empty⌝ ∨ hardStatePts p dq hs)

/-- An optional `*HardState` (a `Ready`'s: `nil` when unchanged). -/
def hsOpt (p : Loc) : Option HardState → IProp GF
  | none => iprop(⌜p = null⌝)
  | some hs => hardStatePts p DFrac.discard hs

/-- An optional `*Snapshot` (a `Ready`'s: `nil` when none), read-only (raft keeps it until
`Advance`). -/
def snapOpt (p : Loc) : Option Snapshot → IProp GF
  | none => iprop(⌜p = null⌝)
  | some s => snapshotPts p DFrac.discard s

/-- What the client gets of a `Ready` message: the whole message, except a response
(`MsgAppResp`, `MsgVoteResp`, ...), which raft reads again after the hand-out (`acceptReady`;
`nonissues/raft-ready-messages-read-after-handout.md`): read-only. -/
def readyDq (m : Msg) : DFrac := if isResponseMsgType m.type then DFrac.discard else DFrac.own 1

/-- A `Ready`'s `Messages`: the slice (the client's) of pointers to the messages. -/
def readyMsgsOwn (sl : GoSlice) (ms : List Msg) : IProp GF :=
  iprop(∃ ps : List Loc, ownSlice sl ps (DFrac.own 1) ∗ ⌜ps.length = ms.length⌝ ∗
    [∗list] pm ∈ ps.zip ms, msgPts pm.1 (readyDq pm.2) pm.2)

/-- **The Go `Ready` value `rd` holds batch `b`** (its committed entries from index `dfrom + 1`). -/
def readyOwn (rd : go_etcd_io.raft.v3.Ready) (dfrom : Nat) (b : Batch) : IProp GF :=
  iprop(softStateOpt rd.SoftState' b.soft ∗ hsOpt rd.HardState' b.hs ∗
    readStatesRO rd.ReadStates' b.reads ∗ entriesRO rd.Entries' b.entsFrom b.ents ∗
    snapOpt rd.Snapshot' b.snap ∗ entriesRO rd.CommittedEntries' (dfrom + 1) b.committed ∗
    readyMsgsOwn rd.Messages' b.msgs ∗ ⌜rd.MustSync' = b.mustSync⌝)

/-! ## The cluster -/

/-- The committed log extends `l` (from index 1). Persistent. -/
opaque committedLb (γ : Cluster) (l : List LogEntry) : IProp GF := iprop(True)

/-- **The client's view of the committed operations** (`opsOf` of the committed log): exclusive,
client-owned; moved only by the proposals' updates. -/
opaque committedOps (γ : Cluster) (ops : List LogEntry) : IProp GF := iprop(True)

/-- The configuration after the first `k` committed entries is `m`. Persistent. -/
opaque confAt (γ : Cluster) (k : Nat) (m : Membership) : IProp GF := iprop(True)

/-- The decisions taken so far on committed conf-change entries (index `k`, from 0, the entry at
index `k + 1`): exclusive, client-owned. -/
opaque confDecisions (γ : Cluster) (D : GMap Nat ConfDecision) : IProp GF := iprop(True)

/-- The decision on the conf-change entry at position `k` (index `k + 1`). Persistent. -/
opaque confDecided (γ : Cluster) (k : Nat) (d : ConfDecision) : IProp GF := iprop(True)

/-- The conf-change entries of `l` at positions `[a, b)` are all decided `skip` (a node whose view
is at `a` and whose delivered log is `b` long has nothing left to apply). -/
def confSkipped (γ : Cluster) (l : List LogEntry) (a b : Nat) : IProp GF :=
  iprop([∗list] j ∈ List.range' a (b - a),
    ∀ e, ⌜l[j]? = some e ∧ e.isConfChange⌝ → confDecided γ j ConfDecision.skip)

/-- The snapshots made so far (with their data): exclusive, client-owned. -/
opaque snapsMade (γ : Cluster) (S : List Snapshot) : IProp GF := iprop(True)

/-- **Snapshot `s` is valid**: made (`snapsMade`), non-empty, at a committed prefix (its index and
its last entry's term), with the configuration at a committed point at or after its index.
Persistent. -/
opaque snapValid (γ : Cluster) (s : Snapshot) : IProp GF := iprop(True)

/-- The read contexts registered so far: exclusive, client-owned. -/
opaque readCtxs (γ : Cluster) (U : List (List w8)) : IProp GF := iprop(True)

/-- Read context `c` is registered with the persistent read update whose result is `Q`. -/
opaque readCtx (γ : Cluster) (c : List w8) (Q : List LogEntry → IProp GF) : IProp GF := iprop(True)

/-- A read state `(c, i)`: the read under context `c` was confirmed when the committed log was `i`
long. Persistent. -/
opaque readState (γ : Cluster) (c : List w8) (i : w64) : IProp GF := iprop(True)

/-- Message `m` was sent by a node of `γ` (in a `Ready`, permitted by its update). Persistent. -/
opaque msgSent (γ : Cluster) (m : Msg) : IProp GF := iprop(True)

/-- The proposal updates message `m` carries (none unless it is a `MsgProp`). Exclusive, or
persistent when `γ.dup`. -/
opaque msgCredit (γ : Cluster) (m : Msg) : IProp GF := iprop(True)

/-- The ids handed out so far (the bootstrap voters' and every `freshIds_take`'s): exclusive. -/
opaque freshIds (γ : Cluster) (U : List w64) : IProp GF := iprop(True)

/-- **Node `id`'s durable state is `D`**: exclusive, client-owned; moved only by the `Ready`s'
updates. -/
opaque raftState (γ : Cluster) (id : w64) (D : Durable) : IProp GF := iprop(True)

/-- No node of `id` runs: exclusive; the starts take it, `Stop` gives it back. -/
opaque nodeVacant (γ : Cluster) (id : w64) : IProp GF := iprop(True)

/-- The cluster's bootstrap log (`[]` for a cluster whose nodes start from a configuration in
their storage). Persistent. -/
opaque bootLog (γ : Cluster) (boot : List LogEntry) : IProp GF := iprop(True)

/-! ## Nodes -/

/-- `n` is a node of `γ` with id `id` (a `*node`, or a `*RawNode`'s location for the
`RawNode`-keyed predicates). Persistent. -/
opaque isNode (n : Loc) (γ : Cluster) (id : w64) : IProp GF := iprop(True)

/-- Node `n` runs (fraction `q`; `Stop` takes it whole). -/
opaque nodeRunning (n : Loc) (q : Qp) : IProp GF := iprop(True)

/-- Node `n` has stopped. Persistent. -/
opaque nodeStopped (n : Loc) : IProp GF := iprop(True)

/-- **The `Ready` loop's token** of node `n`, at driver state `st`: exclusive. The `Ready` receive
takes it, the batch's `readyEnter` gives it back, `Advance` takes and gives it. -/
opaque nodeDriver (n : Loc) (γ : Cluster) (st : Driver) : IProp GF := iprop(True)

/-- **Node `n`'s configuration view**: its tracker holds `v.membership`, the configuration after
the first `v.applied` committed entries. Exclusive (the thread applying conf changes holds it). -/
opaque nodeConf (n : Loc) (γ : Cluster) (v : ConfView) : IProp GF := iprop(True)

/-- The committed log delivered to node `n` (its `Ready`s' committed entries) extends `l`.
Persistent. -/
opaque deliveredLb (n : Loc) (γ : Cluster) (l : List LogEntry) : IProp GF := iprop(True)

/-- Node `n`'s applied index (the delivered log as of its last `Advance`), or the index of a snapshot
installed in its storage and not yet `Advance`d, is at least `i` (round 2, R3: between
`readyStor_install` and `Advance` the storage's compaction point is the new snapshot's index while
raft's applied index is still below it). Persistent. -/
opaque appliedLb (n : Loc) (i : Nat) : IProp GF := iprop(True)

/-- Node `n`'s storage presents its contents through `S` (fixed at the start). Persistent. -/
opaque nodeStorage (n : Loc) (γ : Cluster) (S : StorState → IProp GF) : IProp GF := iprop(True)

/-- Node `n`'s storage holds a snapshot at index `j` or later. Persistent. -/
opaque storSnapLb (n : Loc) (j : Nat) : IProp GF := iprop(True)

/-- **The storage writes of the current batch still to do**: install `s` (if `some`), then append
`es` at index `k`. Exclusive; the `Ready` gives it, `Advance` takes it with nothing left. -/
opaque readyStor (n : Loc) (s : Option Snapshot) (k : Nat) (es : List LogEntry) : IProp GF :=
  iprop(True)

/-- `ch` is node `n`'s `Ready` channel. Persistent. -/
opaque isReadyChan (n : Loc) (ch : Loc) : IProp GF := iprop(True)

/-- **A `RawNode`'s token** (`rn`, node `id` of `γ`): exclusive (a `RawNode` is not thread-safe;
every method takes it). It stands for a `node`'s `isNode`; the other node predicates are keyed by
`rn` (`nodeRunning rn`, `nodeDriver rn`, `nodeConf rn`, ...), as for a `node`. -/
opaque rawNode (rn : Loc) (γ : Cluster) (id : w64) : IProp GF := iprop(True)

/-! ### Internal (node.go's own helpers; no client sees them) -/

/-- (internal) What the run goroutine of node `n` holds: its `RawNode` (and that `RawNode`'s
token) and the loop's local state. -/
opaque nodeLoop (n : Loc) : IProp GF := iprop(True)

/-- (internal) A `node` value `nv` fresh from `newNode`: its channels new, its `rn` the `RawNode`
(whose token it holds) of node `id` of `γ`. -/
opaque nodeFresh (nv : go_etcd_io.raft.v3.node) (rn : Loc) (γ : Cluster) (id : w64) : IProp GF :=
  iprop(True)

/-- (internal) What `raft.Step` needs of a message node `n` steps for its client: a received
message's `msgSent`, credit and address, or a local proposal (`MsgProp`) with its client's update,
or a local message of the node API (`MsgHup`, `MsgReadIndex` with its registered context, ...). -/
opaque stepOk (n : Loc) (γ : Cluster) (id : w64) (m : Msg) : IProp GF := iprop(True)

/-! ## Storage -/

/-- **A detached-or-shared `MemoryStorage`'s contents are `σ`**: exclusive. -/
opaque memStor (ms : Loc) (σ : StorState) : IProp GF := iprop(True)

end vocab

section govocab
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
  {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
  [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `e` is the value of raft's error variable `g` (`ErrStopped`, `ErrCompacted`, ...). -/
def errIs (g : GoString) (e : GoInterface) : IProp GF := iprop(globalAddr g ↦□ e)

/-- A `*MemoryStorage` as a `Storage`. -/
def memStorIface (ms : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType go_etcd_io.raft.v3.MemoryStorage.ty) #ms

/-- A `*node` as a `Node`. -/
def nodeIface (n : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType go_etcd_io.raft.v3.node.ty) #n

/-- **raft's `Storage` contract** for interface value `st` whose contents `S` presents, with
`InitialState`'s configuration `cf σ` (a `MemoryStorage`'s: its snapshot's). The interface's
methods, as raft calls them (from its goroutine only):
- `InitialState`, on a storage no one else touches (raft calls it only while starting): the stored
  hard state (`nil` for the empty one) and configuration;
- `Entries(lo, hi, max)`, `lo < hi ≤ last + 1`: `ErrCompacted` exactly at or below the compaction
  point, else a non-empty prefix of the stored entries `[lo, hi)`, in a slice with no spare
  capacity (raft's log extends it: R3's request) (round 1, F7: no `ErrUnavailable`, on which raft
  panics);
- `Term(i)`, `i ≤ last` (raft asks no further): the stored term at `i`, or `ErrCompacted` below the
  compaction point;
- `LastIndex`, `FirstIndex`;
- `Snapshot`: the stored snapshot (a fresh copy), or `ErrSnapshotTemporarilyUnavailable`.
Each but `InitialState` is atomic (raft holds `S` in its invariant while the client writes). -/
def isStorage (st : GoInterface) (S : StorState → IProp GF) (cf : StorState → ConfState) :
    IProp GF :=
  iprop(∃ i : GoInterfaceOk, ⌜st = interface.ok i⌝ ∗
    (□ ∀ (σ : StorState) (Φ : val → IProp GF), S σ -∗
      ▷ (∀ hp csp, S σ ∗ hsPtr hp DFrac.discard σ.hs ∗ confStatePts csp DFrac.discard (cf σ) -∗
          Φ (PairV (PairV #hp #csp) #interface.nil)) -∗
      WP (App (Val #(methods i.ty go!"InitialState" i.v)) (Val #())) {{ Φ }}) ∗
    (□ ∀ (lo hi mx : w64) (Φ : val → IProp GF),
      (AU <{ ∃∃ σ, S σ ∗ ⌜uint.nat lo < uint.nat hi ∧ uint.nat hi ≤ σ.last + 1⌝ }> @ ⊤, ∅
        <{ S σ, COMM ∀ (sl : GoSlice) (err : GoInterface),
            ((⌜uint.nat lo ≤ σ.off⌝ ∗ errIs go_etcd_io.raft.v3.ErrCompacted err) ∨
             (⌜err = interface.nil ∧ σ.off < uint.nat lo ∧ sl.len = sl.cap⌝ ∗
                ∃ es, entriesRO sl (uint.nat lo) es ∗
                ⌜es ≠ [] ∧ es <+: (σ.ents.drop (uint.nat lo - σ.off - 1)).take
                  (uint.nat hi - uint.nat lo)⌝)) -∗
            Φ (PairV #sl #err) }>) -∗
      WP (App (App (App (Val #(methods i.ty go!"Entries" i.v)) (Val #lo)) (Val #hi)) (Val #mx))
        {{ Φ }}) ∗
    (□ ∀ (j : w64) (Φ : val → IProp GF),
      (AU <{ ∃∃ σ, S σ ∗ ⌜uint.nat j ≤ σ.last⌝ }> @ ⊤, ∅
        <{ S σ, COMM ∀ (t : w64) (err : GoInterface),
            ((⌜err = interface.nil ∧ σ.termAt (uint.nat j) = some t⌝) ∨
             (⌜uint.nat j < σ.off⌝ ∗ errIs go_etcd_io.raft.v3.ErrCompacted err)) -∗
            Φ (PairV #t #err) }>) -∗
      WP (App (Val #(methods i.ty go!"Term" i.v)) (Val #j)) {{ Φ }}) ∗
    (□ ∀ (Φ : val → IProp GF),
      (AU <{ ∃∃ σ, S σ }> @ ⊤, ∅
        <{ S σ, COMM Φ (PairV #(W64 σ.last) #interface.nil) }>) -∗
      WP (App (Val #(methods i.ty go!"LastIndex" i.v)) (Val #())) {{ Φ }}) ∗
    (□ ∀ (Φ : val → IProp GF),
      (AU <{ ∃∃ σ, S σ }> @ ⊤, ∅
        <{ S σ, COMM Φ (PairV #(W64 σ.first) #interface.nil) }>) -∗
      WP (App (Val #(methods i.ty go!"FirstIndex" i.v)) (Val #())) {{ Φ }}) ∗
    (□ ∀ (Φ : val → IProp GF),
      (AU <{ ∃∃ σ, S σ }> @ ⊤, ∅
        <{ S σ, COMM ∀ (sp : Loc) (err : GoInterface),
            ((⌜err = interface.nil⌝ ∗ snapshotPts sp (DFrac.own 1) σ.snap) ∨
             errIs go_etcd_io.raft.v3.ErrSnapshotTemporarilyUnavailable err) -∗
            Φ (PairV #sp #err) }>) -∗
      WP (App (Val #(methods i.ty go!"Snapshot" i.v)) (Val #())) {{ Φ }}))

/-- **raft's `Logger` contract** for `lg`: its methods other than `Fatal*`/`Panic*` return (raft
calls those only where it is about to fail anyway, which a proof rules out). Persistent; etcd's zap
adapter and the examples' loggers meet it (their batches' laws). -/
opaque loggerOk (lg : GoInterface) : IProp GF := iprop(True)

/-- **A node's error**: `nil`, `ErrStopped` (the node has stopped), or the error of `ctx`, which is
done. -/
def nodeErr (n : Loc) (ctx : GoInterface) (err : GoInterface) : IProp GF :=
  iprop(⌜err = interface.nil⌝ ∨ (errIs go_etcd_io.raft.v3.ErrStopped err ∗ nodeStopped n) ∨
    (Context.ctxDone ctx ∗ context.isCtxErr err))

/-- **A proposal's error**: a node's, or `ErrProposalDropped` (no leader, a leader transfer, a
conf change while one is pending, ...: the proposal may still have been forwarded and commit). -/
def propErr (n : Loc) (ctx : GoInterface) (err : GoInterface) : IProp GF :=
  iprop(nodeErr n ctx err ∨ errIs go_etcd_io.raft.v3.ErrProposalDropped err)

/-- **The update a `Ready` hands out to enter its batch** `b` (from driver state `st`, delivered log
after it `dl`): fired once, when the client makes the batch durable (or at once), at node `n`'s
current durable state; gives the new durable state, the driver back (for `Advance`), the
permission to send the batch's messages and the read states. -/
def readyEnter (n : Loc) (γ : Cluster) (id : w64) (st : Driver) (b : Batch) (dl : List LogEntry) :
    IProp GF :=
  iprop(∀ (E : CoPset) (q : Qp), ⌜↑γ.ns ⊆ E⌝ -∗
    raftState γ id st.durable ∗ nodeRunning n q ={E}=∗
      raftState γ id (st.durable.next b) ∗ nodeRunning n q ∗ nodeDriver n γ (st.after b dl) ∗
      ([∗list] m ∈ b.msgs, msgSent γ m) ∗ ([∗list] r ∈ b.reads, readState γ r.1 r.2))

/-- **The persistent check a `Ready` hands out**: at the batch's starting durable state (before it
is entered), the read states, and the messages if the batch leaves the node leader (a leader may
send before its write: Raft thesis 10.2.1, etcd's `raftNode.start`). -/
def readyCheck (n : Loc) (γ : Cluster) (id : w64) (st : Driver) (b : Batch) : IProp GF :=
  iprop(□ ∀ (E : CoPset) (q : Qp), ⌜↑γ.ns ⊆ E⌝ -∗
    raftState γ id st.durable ∗ nodeRunning n q ={E}=∗
      raftState γ id st.durable ∗ nodeRunning n q ∗
      ([∗list] r ∈ b.reads, readState γ r.1 r.2) ∗
      (⌜(b.soft.map (·.2)).getD st.role = StateLeader⌝ -∗ [∗list] m ∈ b.msgs, msgSent γ m))

/-- **What a `Ready` gives** (node `n`, from driver state `st`): its batch `b` and the Go values
holding it, the facts it states (`BatchOk`; its `MsgApp`s are from `id`: 2f's request), the committed log after it (`dl`: a snapshot's prefix,
or the delivered log with the committed entries) with the snapshot's validity, the messages'
credits, the storage writes to do, and the two updates. -/
def readyGot (n : Loc) (γ : Cluster) (id : w64) (st : Driver) (rd : go_etcd_io.raft.v3.Ready) :
    IProp GF :=
  iprop(∃ (b : Batch) (dl : List LogEntry),
    readyOwn rd st.delivered.length b ∗ ⌜BatchOk st b⌝ ∗
    ⌜∀ m ∈ b.msgs, m.type = MsgApp → m.src = id⌝ ∗
    committedLb γ dl ∗ deliveredLb n γ dl ∗
    (match b.snap with
     | none => ⌜dl = st.delivered ++ b.committed⌝
     | some s => snapValid γ s ∗ ⌜dl.length = uint.nat s.index ∧ st.delivered <+: dl⌝) ∗
    ([∗list] m ∈ b.msgs, msgCredit γ m) ∗
    readyStor n b.snap b.entsFrom b.ents ∗
    readyEnter n γ id st b dl ∗ readyCheck n γ id st b)

/-- **A valid configuration** (`Config.validate` accepts it, and what raft's proof needs of the
options): a non-zero, non-local id; `0 < HeartbeatTick < ElectionTick`; a storage; some inflight
messages, and inflight bytes (if limited) for a message; a per-message or per-`Ready` size limit
(`issues/raft-zero-max-size-per-msg.md`: both `0` panics). **The ring capacity** `MaxInflightMsgs ≤
2^62` (`Tracker.inflightsMax`: `NewInflights`' `int` index arithmetic does not wrap below it; Go
cannot allocate a ring that large, Perennial's model has no memory bound): R4's proposal, an **open
question for the user** (R4's question 1; etcd uses 4096, the examples 256). **Scope** (no client of this repository
or etcd sets them): `ReadOnlyOption` is `ReadOnlySafe` (a lease-based read is linearizable only
under clock assumptions), `AsyncStorageWrites` is off, `DisableConfChangeValidation` is off. Any
`CheckQuorum`, `PreVote`, `StepDownOnRemoval`, `DisableProposalForwarding`, size limits. -/
def ConfigOk (cv : go_etcd_io.raft.v3.Config) : Prop :=
  cv.ID' ≠ W64 0 ∧ isLocalTarget cv.ID' = false ∧
  0 < sint.Z cv.HeartbeatTick' ∧ sint.Z cv.HeartbeatTick' < sint.Z cv.ElectionTick' ∧
  cv.Storage' ≠ interface.nil ∧ 0 < sint.Z cv.MaxInflightMsgs' ∧
  sint.Z cv.MaxInflightMsgs' ≤ Tracker.inflightsMax ∧
  (cv.MaxInflightBytes' = W64 0 ∨ uint.nat cv.MaxSizePerMsg' ≤ uint.nat cv.MaxInflightBytes') ∧
  (cv.MaxSizePerMsg' ≠ W64 0 ∨ cv.MaxCommittedSizePerReady' ≠ W64 0) ∧
  cv.ReadOnlyOption' = W64 0 ∧ cv.AsyncStorageWrites' = false ∧
  cv.DisableConfChangeValidation' = false

end govocab

/-! ## Laws

Obligations of raft's proof, used by its clients. Grouped by predicate. -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
  {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
  [package_sem : go_etcd_io.raft.v3.Assumptions]

/-! ### Persistence, timelessness, exclusivity -/

/-- (raftpb's predicates' persistence is raftpb's law, `RaftPb.raftpb_persistent.spec`; `entriesRO`
is a definition over them.) -/
def persistent.spec : Prop :=
  (∀ p o, Persistent (softStateOpt (GF := GF) p o)) ∧
  (∀ sl rs, Persistent (readStatesRO (GF := GF) sl rs)) ∧
  (∀ γ l, Persistent (committedLb (GF := GF) γ l)) ∧
  (∀ γ k m, Persistent (confAt (GF := GF) γ k m)) ∧
  (∀ γ k d, Persistent (confDecided (GF := GF) γ k d)) ∧
  (∀ γ s, Persistent (snapValid (GF := GF) γ s)) ∧
  (∀ γ c Q, Persistent (readCtx (GF := GF) γ c Q)) ∧
  (∀ γ c i, Persistent (readState (GF := GF) γ c i)) ∧
  (∀ γ m, Persistent (msgSent (GF := GF) γ m)) ∧
  (∀ γ b, Persistent (bootLog (GF := GF) γ b)) ∧
  (∀ n γ id, Persistent (isNode (GF := GF) n γ id)) ∧
  (∀ n, Persistent (nodeStopped (GF := GF) n)) ∧
  (∀ n γ l, Persistent (deliveredLb (GF := GF) n γ l)) ∧
  (∀ n i, Persistent (appliedLb (GF := GF) n i)) ∧
  (∀ n γ S, Persistent (nodeStorage (GF := GF) n γ S)) ∧
  (∀ n j, Persistent (storSnapLb (GF := GF) n j)) ∧
  (∀ n ch, Persistent (isReadyChan (GF := GF) n ch))

/-- The client-owned states are timeless (a client keeps them in its invariants). -/
def timeless.spec : Prop :=
  (∀ γ l, Timeless (committedLb (GF := GF) γ l)) ∧
  (∀ γ ops, Timeless (committedOps (GF := GF) γ ops)) ∧
  (∀ γ k m, Timeless (confAt (GF := GF) γ k m)) ∧
  (∀ γ D, Timeless (confDecisions (GF := GF) γ D)) ∧
  (∀ γ k d, Timeless (confDecided (GF := GF) γ k d)) ∧
  (∀ γ S, Timeless (snapsMade (GF := GF) γ S)) ∧
  (∀ γ U, Timeless (readCtxs (GF := GF) γ U)) ∧
  (∀ γ id D, Timeless (raftState (GF := GF) γ id D)) ∧
  (∀ γ id, Timeless (nodeVacant (GF := GF) γ id)) ∧
  (∀ ms σ, Timeless (memStor (GF := GF) ms σ))

def exclusive.spec : Prop :=
  (∀ γ o1 o2, committedOps (GF := GF) γ o1 ∗ committedOps γ o2 ⊢ iprop(False)) ∧
  (∀ γ D1 D2, confDecisions (GF := GF) γ D1 ∗ confDecisions γ D2 ⊢ iprop(False)) ∧
  (∀ γ S1 S2, snapsMade (GF := GF) γ S1 ∗ snapsMade γ S2 ⊢ iprop(False)) ∧
  (∀ γ U1 U2, readCtxs (GF := GF) γ U1 ∗ readCtxs γ U2 ⊢ iprop(False)) ∧
  (∀ γ U1 U2, freshIds (GF := GF) γ U1 ∗ freshIds γ U2 ⊢ iprop(False)) ∧
  (∀ γ id D1 D2, raftState (GF := GF) γ id D1 ∗ raftState γ id D2 ⊢ iprop(False)) ∧
  (∀ γ id, nodeVacant (GF := GF) γ id ∗ nodeVacant γ id ⊢ iprop(False)) ∧
  (∀ ms σ1 σ2, memStor (GF := GF) ms σ1 ∗ memStor ms σ2 ⊢ iprop(False)) ∧
  (∀ n q, nodeRunning (GF := GF) n q ∗ nodeStopped n ⊢ iprop(False))

def nodeRunning_fractional.spec : Prop := ∀ n, Fractional (nodeRunning (GF := GF) n)

/-! ### Allocation -/

/-- **A new cluster**: voters `ps` (ids and contexts), with the bootstrap log `boot` (`StartNode`'s:
`BootLog ps boot`) or none (the nodes start from a storage holding the configuration). The client
chooses the namespace and the credit mode. It gets the client-owned states (empty, but the
committed bootstrap operations), every voter's durable state (empty) and vacancy, and the ids it
handed out. The configuration: without a bootstrap log, the voters' from index 0; with one, the
empty configuration at index 0 (a node joining later starts there, from an empty storage), each
bootstrap entry decided to apply its `AddNode`, and the voters' after the bootstrap log.

**Open (a user decision; R1's question 9, R2's question 1):** raft's term and index bound. `raft.Step`,
`hup`, the ticks and `stepCandidate` take no term budget: R2's cluster invariant holds a time receipt
per term increase and per appended entry (`ApiCore.lean`'s realization item 5), which bounds every
term and index by the execution's step bound, and that bound must enter here, as an instance binder
(R2's proposal: `∀ [ReceiptBoundLe GF (2^63)]`), at `2^63` so that it also gives R3's local range
premises (every index below `2^63`: `raftLog.slice`/`entries`/`scan`'s `hi - lo < 2^63`, `append`'s
`k + |es| < 2^64`, `maybeAppend`'s, `restore`'s). Not stated until the user decides; without it R2's
`raft.Step` (a campaign at term `2^64 - 1` wraps, `raft.go:926`) and the specs above it are not
provable. -/
def cluster_alloc.spec : Prop :=
  ∀ (N : Namespace) (dup : Bool) (ps : List (w64 × List w8)) (boot : List LogEntry) (E : CoPset),
    let vs := ps.map (·.1)
    ps ≠ [] → vs.Nodup → W64 0 ∉ vs → (∀ id ∈ vs, isLocalTarget id = false) →
    (boot = [] ∨ BootLog ps boot) →
    ⊢ |={E}=> ∃ γ : Cluster, ⌜γ.ns = N ∧ γ.dup = dup⌝ ∗
      committedOps (GF := GF) γ (opsOf boot) ∗ committedLb γ boot ∗ bootLog γ boot ∗
      confAt γ boot.length (Membership.simple (listToSet vs)) ∗
      (if boot = [] then confDecisions γ ∅ else
        confAt γ 0 Membership.empty ∗
        ∃ D, confDecisions γ D ∗ [∗list] k ∈ List.range boot.length,
          ∃ p : w64 × List w8, ⌜ps[k]? = some p⌝ ∗
            confDecided γ k (.apply (.v1 ⟨ConfChangeAddNode, p.1, p.2, W64 0⟩))) ∗
      snapsMade γ [] ∗ readCtxs γ [] ∗ freshIds γ vs ∗
      [∗list] id ∈ vs, raftState γ id Durable.init ∗ nodeVacant γ id

/-- **A new id** (a node joining later, from an empty storage): its empty durable state and its
vacancy. An id is handed out once: a node that lost its state must never run under its old id. -/
def freshIds_take.spec : Prop :=
  ∀ (γ : Cluster) (U : List w64) (id : w64), id ∉ U → id ≠ W64 0 → isLocalTarget id = false →
    freshIds (GF := GF) γ U ⊢ |==> freshIds γ (id :: U) ∗ raftState γ id Durable.init ∗
      nodeVacant γ id

/-- **The bootstrap entries' decisions** (R2's request, round 1 item 10: `RawNode.Bootstrap`'s proof
applies each bootstrap `AddNode` through `raft.applyConfChange.spec`, which takes the entry's
decision): each entry of a bootstrap log is decided to apply its `AddNode` (`cluster_alloc` decided
them; persistent, so every founder's `Bootstrap` reads them). (Integration I2.) -/
def bootLog_decided.spec : Prop :=
  ∀ γ (ps : List (w64 × List w8)) (boot : List LogEntry), BootLog ps boot →
    bootLog (GF := GF) γ boot ⊢ [∗list] k ∈ List.range boot.length,
      ∃ p : w64 × List w8, ⌜ps[k]? = some p⌝ ∗
        confDecided γ k (.apply (.v1 ⟨ConfChangeAddNode, p.1, p.2, W64 0⟩))

/-! ### The committed log -/

def committedLb_nil.spec : Prop := ∀ γ, ⊢ committedLb (GF := GF) γ []

def committedLb_mono.spec : Prop :=
  ∀ γ (l1 l2 : List LogEntry), l1 <+: l2 → committedLb (GF := GF) γ l2 ⊢ committedLb γ l1

def committedLb_agree.spec : Prop :=
  ∀ γ (l1 l2 : List LogEntry), committedLb (GF := GF) γ l1 ∗ committedLb γ l2 ⊢
    iprop(⌜l1 <+: l2 ∨ l2 <+: l1⌝)

/-- The client's operations contain every committed prefix's. -/
def committedOps_lb.spec : Prop :=
  ∀ γ ops (l : List LogEntry), committedOps (GF := GF) γ ops ∗ committedLb γ l ⊢
    iprop(⌜opsOf l <+: ops⌝)

/-- ... and are exactly some committed prefix's. -/
def committedOps_get_lb.spec : Prop :=
  ∀ γ ops, committedOps (GF := GF) γ ops ⊢
    committedOps γ ops ∗ ∃ l, committedLb γ l ∗ ⌜opsOf l = ops⌝

/-- Committed conf-change entries decode (they were built by `ProposeConfChange` or a bootstrap). -/
def committedLb_confDecodes.spec : Prop :=
  ∀ γ (l : List LogEntry), committedLb (GF := GF) γ l ⊢
    iprop(⌜∀ e ∈ l, e.isConfChange → ∃ c, decodeConfChange e.type e.data = some c ∧
      c.entryType = e.type⌝)

/-! ### Configurations -/

def confAt_agree.spec : Prop :=
  ∀ γ k (m1 m2 : Membership), confAt (GF := GF) γ k m1 ∗ confAt γ k m2 ⊢ iprop(⌜m1 = m2⌝)

/-- Every configuration of the cluster is valid (the empty one at index 0 included). (Round 1, S4.) -/
def confAt_valid.spec : Prop := ∀ γ k (m : Membership), confAt (GF := GF) γ k m ⊢ iprop(⌜m.Valid⌝)

/-- A configuration point is within the committed log. -/
def confAt_committed.spec : Prop :=
  ∀ γ k (m : Membership), confAt (GF := GF) γ k m ⊢ ∃ l, committedLb γ l ∗ ⌜k ≤ l.length⌝

/-- **An empty `EntryConfChangeV2` (leave joint) is committed only at a joint configuration**: raft
appends one itself only when joint with auto-leave, and the leader refuses a client's leave
proposal at a configuration that is not joint (validation on: `ConfigOk`). (Round 1, completeness
F2: etcd's apply panics on any entry type but `EntryNormal`/`EntryConfChange`.) -/
def committedLb_emptyV2.spec : Prop :=
  ∀ γ (l : List LogEntry) k e (m : Membership), l[k]? = some e → e.isEmptyV2 →
    committedLb (GF := GF) γ l ∗ confAt γ k m ⊢ iprop(⌜m.isJoint⌝)

/-- An entry that is no conf change keeps the configuration. -/
def confAt_normal.spec : Prop :=
  ∀ γ (l : List LogEntry) k e (m : Membership), l[k]? = some e → ¬ e.isConfChange →
    committedLb (GF := GF) γ l ∗ confAt γ k m ⊢ confAt γ (k + 1) m

/-- A decided conf-change entry moves the configuration by the decision. -/
def confAt_decided.spec : Prop :=
  ∀ γ k (m : Membership) d, confAt (GF := GF) γ k m ∗ confDecided γ k d ⊢
    ∃ m', ⌜d.step m = some m'⌝ ∗ confAt γ (k + 1) m'

/-- Skipped entries keep the configuration. -/
def confAt_skipped.spec : Prop :=
  ∀ γ (l : List LogEntry) a b (m : Membership), a ≤ b → b ≤ l.length →
    committedLb (GF := GF) γ l ∗ confAt γ a m ∗ confSkipped γ l a b ⊢ confAt γ b m

/-- **Decide** a committed conf-change entry (once, for the cluster): to apply a change that is
defined at the configuration before it, or to skip it. -/
def confDecide.spec : Prop :=
  ∀ γ (D : GMap Nat ConfDecision) (l : List LogEntry) k e (m m' : Membership) d,
    D !! k = none → l[k]? = some e → e.isConfChange → d.step m = some m' →
    confDecisions (GF := GF) γ D ∗ committedLb γ l ∗ confAt γ k m ⊢ |==>
      confDecisions γ (<[k := d]> D) ∗ confDecided γ k d

def confDecided_agree.spec : Prop :=
  ∀ γ k (d1 d2 : ConfDecision), confDecided (GF := GF) γ k d1 ∗ confDecided γ k d2 ⊢
    iprop(⌜d1 = d2⌝)

def confDecisions_lookup.spec : Prop :=
  ∀ γ (D : GMap Nat ConfDecision) k d, confDecisions (GF := GF) γ D ∗ confDecided γ k d ⊢
    iprop(⌜D !! k = some d⌝)

/-- A node's view is the cluster's configuration at its index. -/
def nodeConf_confAt.spec : Prop :=
  ∀ n γ (v : ConfView), nodeConf (GF := GF) n γ v ⊢ nodeConf n γ v ∗ confAt γ v.applied v.membership

/-! #### What a change does (confchange's model, R4): the cases clients rely on

`Membership.applyChange` is now a definition (confchange's `changeV2`, `Model.lean`); these laws are
instances of R4's (`ConfChange.simple_valid`, `changeV2_valid`, `changeV2_single`), kept under the
names the node API's clients cite. -/

/-- A configuration of voters only, without id `0`, is valid (the empty one included). (Integration
I2: R4's `ConfChange.simple_valid.spec`; the premises non-empty, no local target and the size bound
were not needed.) -/
def Membership.simple_valid.spec : Prop :=
  ∀ (vs : List w64), W64 0 ∉ vs → (Membership.simple (listToSet vs)).Valid

/-- A change keeps a configuration valid (R4's `ConfChange.changeV2_valid.spec`). -/
def Membership.applyChange_valid.spec : Prop :=
  ∀ c (m m' : Membership), m.Valid → Membership.applyChange c m = some m' → m'.Valid

open Classical in
/-- **A legacy change at a configuration that is not joint** (the empty one included: the
bootstrap's `AddNode`s): the change (`ConfChange.applyOne`: node `0` and `UpdateNode` change
nothing, `AddNode` makes a voter, `AddLearnerNode` a learner, `RemoveNode` removes, an unknown type
is an error), then an error if no voter is left. (Integration I2: R4's `changeV2_single.spec`; the
round-0 statement was false in two cases, R4's finding: at the empty configuration a no-op is the
error "removed all voters", and an unknown type is an error, not a removal.) -/
def Membership.applyChange_v1.spec : Prop :=
  ∀ (cc : ConfChangeV1) (m : Membership), m.Valid → ¬ m.isJoint →
    Membership.applyChange (.v1 cc) m =
      (ConfChange.applyOne ⟨cc.type, cc.nodeId⟩ m).bind
        (fun m' => if m'.voters = ∅ then none else some m')

/-! ### Snapshots -/

/-- **Make a snapshot** of a committed prefix `l`, with the configuration at a committed point `a`
at or after it (its own index, or later: etcd records the backend's configuration, which may be
ahead of the snapshot's index during a replay, `nonissues/etcd-replay-snapshot-confstate-ahead.md`),
with any data: the client records it (and may keep any invariant of its data). A node installing
it takes the configuration at `a` (`node.Advance.spec`) and re-applies nothing below `a`.
(Round 1, completeness F3: generalized from `a = |l|`.) -/
def snap_make.spec : Prop :=
  ∀ γ (S : List Snapshot) (l : List LogEntry) (a : Nat) (m : Membership) (s : Snapshot),
    0 < l.length → uint.nat s.index = l.length → termAt l l.length = some s.term →
    l.length ≤ a → s.conf.Is m →
    snapsMade (GF := GF) γ S ∗ committedLb γ l ∗ confAt γ a m ⊢ |==>
      snapsMade γ (s :: S) ∗ snapValid γ s

def snapValid_made.spec : Prop :=
  ∀ γ (S : List Snapshot) s, snapsMade (GF := GF) γ S ∗ snapValid γ s ⊢ iprop(⌜s ∈ S⌝)

def snapValid_committed.spec : Prop :=
  ∀ γ (s : Snapshot), snapValid (GF := GF) γ s ⊢
    ∃ (l : List LogEntry) (a : Nat) (m : Membership), committedLb γ l ∗ confAt γ a m ∗
      ⌜0 < l.length ∧ uint.nat s.index = l.length ∧ termAt l l.length = some s.term ∧
        l.length ≤ a ∧ s.conf.Is m⌝

/-! ### Reads -/

/-- **Register a read**: a fresh context with a persistent update (the read: at the committed
operations when it is confirmed). -/
def readCtx_register.spec : Prop :=
  ∀ γ (U : List (List w8)) c (Q : List LogEntry → IProp GF), c ∉ U →
    readCtxs (GF := GF) γ U ∗
      □ (AU <{ ∃∃ ops, committedOps γ ops }> @ ⊤ \ ↑γ.ns, ∅
          <{ committedOps γ ops, COMM □ Q ops }>) ⊢ |==>
      readCtxs γ (c :: U) ∗ readCtx γ c Q

/-- **A read state answers its read**: the update fired when the committed log was `i` long; once
the client knows the log that far, it gets the read's result at it. -/
def readState_fire.spec : Prop :=
  ∀ γ c (i : w64) (Q : List LogEntry → IProp GF) (l : List LogEntry) (E : CoPset),
    ↑γ.ns ⊆ E → uint.nat i ≤ l.length →
    readState (GF := GF) γ c i ∗ readCtx γ c Q ∗ committedLb γ l ⊢ |={E}=>
      ∃ l', committedLb γ l' ∗ ⌜l'.length = uint.nat i⌝ ∗ ▷ ▷ □ Q (opsOf l')

/-- Only registered contexts are answered. -/
def readState_registered.spec : Prop :=
  ∀ γ c (i : w64) (U : List (List w8)), readState (GF := GF) γ c i ∗ readCtxs γ U ⊢
    iprop(⌜c ∈ U⌝)

/-! ### Messages -/

/-- A message that carries no proposal needs no credit. -/
def msgCredit_intro.spec : Prop :=
  ∀ γ (m : Msg), m.type ≠ MsgProp → ⊢ |==> msgCredit (GF := GF) γ m

/-- With persistent credits, a message's credit may be copied (a transport that duplicates). -/
def msgCredit_dup.spec : Prop :=
  ∀ γ (m : Msg), γ.dup = true → msgCredit (GF := GF) γ m ⊢ □ msgCredit γ m

/-- A sent message has one of raftpb's message types (`IsLocalMsg`/`IsResponseMsg` index an array
by it: a negative one panics). -/
def msgSent_type.spec : Prop :=
  ∀ γ (m : Msg), msgSent (GF := GF) γ m ⊢ iprop(⌜0 ≤ sint.Z m.type ∧ sint.Z m.type ≤ 23⌝)

/-- A sent `MsgSnap` carries a valid snapshot. -/
def msgSent_snap.spec : Prop :=
  ∀ γ (m : Msg), m.type = MsgSnap → msgSent (GF := GF) γ m ⊢
    ∃ s, ⌜m.snapshot = some s⌝ ∗ snapValid γ s

/-- **The shape of a sent `MsgApp`** (raft's one constructor, `maybeSendAppend`, sets only `To`,
`Type`, `Index`, `LogTerm`, `Entries`, `Commit`; `send` sets `From` and `Term`): no vote, snapshot,
rejection, hint or context. rafthttp's msgappv2 short frame carries only the entries and the commit
and rebuilds the rest (2f's request, `req/go_etcd_io_raft_v3.md`, "from 2f, round 1"; integration
I2). -/
def msgSent_appShape.spec : Prop :=
  ∀ γ (m : Msg), m.type = MsgApp → msgSent (GF := GF) γ m ⊢
    iprop(⌜m.vote = W64 0 ∧ m.snapshot = none ∧ m.reject = false ∧ m.rejectHint = W64 0 ∧
      m.context = []⌝)

/-- **A sent `MsgSnap` has a non-zero term** (it is sent by its term's leader, and terms of leaders
are at least 1): etcd's merged-snapshot guard `m.GetTerm() == raftTerm` excludes a restarted
server whose `raftTerm` is still `0` (2d's request, round 1, item 3; integration I2). -/
def msgSent_snapTerm.spec : Prop :=
  ∀ γ (m : Msg), m.type = MsgSnap → msgSent (GF := GF) γ m ⊢ iprop(⌜m.term ≠ W64 0⌝)

/-- **A sent `MsgSnap` may carry a newer valid snapshot instead, of a prefix of the sender's
delivered log** (etcd's merged snapshot message, `createMergedSnapshotMessage`: the server's applied
index, its configuration, no data). The prefix must be the sender's: a snapshot committed at a later
term the sender does not know of would let the sender, still leader at the message's term, count
the follower's acknowledgement of an entry the follower does not hold (round 1, provability F1); and
its term at most the message's: a sender that stepped down may have delivered entries of later
terms, and a follower at the message's term installing them breaks raft
(`issues/etcd-merged-snapshot-stale-term.md`; the fork's guard `m.GetTerm() == apply.raftTerm`,
round 2, N2). -/
def msgSent_replaceSnap.spec : Prop :=
  ∀ γ (m : Msg) (s s' : Snapshot) (n : Loc) (l : List LogEntry), m.type = MsgSnap →
    m.snapshot = some s → uint.nat s.index ≤ uint.nat s'.index → uint.nat s'.index ≤ l.length →
    uint.nat s'.term ≤ uint.nat m.term →
    msgSent (GF := GF) γ m ∗ snapValid γ s' ∗ isNode n γ m.src ∗ deliveredLb n γ l ⊢ |==>
      msgSent γ { m with snapshot := some s' }

/-! ### Nodes -/

/-- What was delivered is committed. -/
def deliveredLb_committed.spec : Prop :=
  ∀ n γ (l : List LogEntry), deliveredLb (GF := GF) n γ l ⊢ committedLb γ l

def deliveredLb_mono.spec : Prop :=
  ∀ n γ (l1 l2 : List LogEntry), l1 <+: l2 → deliveredLb (GF := GF) n γ l2 ⊢ deliveredLb n γ l1

/-- The driver knows what it delivered. -/
def nodeDriver_delivered.spec : Prop :=
  ∀ n γ (st : Driver), nodeDriver (GF := GF) n γ st ⊢
    nodeDriver n γ st ∗ deliveredLb n γ st.delivered

def appliedLb_mono.spec : Prop :=
  ∀ n (i j : Nat), j ≤ i → appliedLb (GF := GF) n i ⊢ appliedLb n j

def storSnapLb_mono.spec : Prop :=
  ∀ n (i j : Nat), j ≤ i → storSnapLb (GF := GF) n i ⊢ storSnapLb n j

/-- **A crash during a batch's durable write** (round 3, 2e's request): with no node of `id` running
(the crashed process gone: `nodeVacant`, which the crash rule of the adequacy theorem gives back)
and the batch's enter update not fired (the evidence that `b` is the batch raft handed out at the
durable state `D`), the client may move its `raftState` to any state the crash left:
`D.crashed b j hs` for a prefix `j` of the batch's entries and a hard state with the old or the
batch's term and vote and a commit between the old `wcommit` and the batch's commit, within the
written log -- provided the result has at most one conf-change entry above its commit
(`confAboveOk`). Raft's safety argument: nothing of the batch was acknowledged (acknowledgements
and votes are sent only after the enter update, at `Advance`, or by a leader whose term and vote the
batch does not change: `readyCheck`), so the node may lose any suffix of it; the condition on conf
entries is what a restart needs (`Durable.confAboveOk`): without it the law is false, by a real
raft bug (`issues/raft-commit-lost-with-entries-kept.md`, reproduced against the pinned raft: two
conf changes kept above a lost commit let the restarted node win in its old configuration and
commit a different entry at an index already committed). Whether etcd may take it as a scope
restriction or the bug blocks etcd's crash restarts is an open question for the user (R1's
question 10). Not covered: a batch with a snapshot. -/
def raftState_crash.spec : Prop :=
  ∀ (n : Loc) γ (id : w64) (st : Driver) (b : Batch) (dl : List LogEntry) (j : Nat)
    (hs : HardState),
    b.snap = none → j ≤ b.ents.length →
    (hs.term = st.durable.term ∧ hs.vote = st.durable.vote ∨
      ∃ h, b.hs = some h ∧ hs.term = h.term ∧ hs.vote = h.vote) →
    uint.nat st.durable.wcommit ≤ uint.nat hs.commit →
    uint.nat hs.commit ≤ uint.nat (b.hs.getD ⟨st.durable.term, st.durable.vote, st.durable.commit⟩).commit →
    uint.nat hs.commit ≤ (st.durable.crashed b j hs).last →
    (st.durable.crashed b j hs).confAboveOk →
    readyEnter (GF := GF) n γ id st b dl ∗ raftState γ id st.durable ∗ nodeVacant γ id ⊢ |==>
      raftState γ id (st.durable.crashed b j hs) ∗ nodeVacant γ id

/-- Dropping a `RawNode` (it has no `Stop`): its id is vacant again. -/
def rawNode_drop.spec : Prop :=
  ∀ rn γ id, rawNode (GF := GF) rn γ id ∗ nodeRunning rn 1 ⊢ |==> nodeVacant γ id

def zero_lbs.spec : Prop :=
  ∀ n, ⊢ appliedLb (GF := GF) n 0 ∗ storSnapLb (GF := GF) n 0

/-! ### Storage writes (the updates raft hands the client)

Each gives an update over the node's storage contents `S`, which raft holds; a storage method's
own spec (`MemoryStorage.Append.spec`, ...) fires it. The update's precondition is what raft
guarantees at the moment of the write (its invariant relates the contents to its log). Their mask
is `⊤`: raft, the update's producer, opens its own invariant (round 1, provability F2). -/

/-- **Install the batch's snapshot**: the storage holds no newer one. -/
def readyStor_install.spec : Prop :=
  ∀ n γ (S : StorState → IProp GF) (s : Snapshot) (k : Nat) (es : List LogEntry),
    readyStor (GF := GF) n (some s) k es ∗ nodeStorage n γ S ⊢
      AU <{ ∃∃ σ, S σ ∗ ⌜σ.applySnapshotErr s = false⌝ }> @ ⊤, ∅
        <{ S (σ.applySnapshot s), COMM readyStor n none k es ∗ storSnapLb n (uint.nat s.index) }>

/-- **Append the batch's entries** (after its snapshot, if any): no gap. -/
def readyStor_append.spec : Prop :=
  ∀ n γ (S : StorState → IProp GF) (k : Nat) (es : List LogEntry),
    readyStor (GF := GF) n none k es ∗ nodeStorage n γ S ⊢
      AU <{ ∃∃ σ, S σ ∗ ⌜(σ.append k es).isSome ∧ k + es.length < 2 ^ 64⌝ }> @ ⊤, ∅
        <{ S ((σ.append k es).getD σ), COMM readyStor n none k [] }>

/-- **Compact** up to the applied index and the stored snapshot. -/
def stor_compact.spec : Prop :=
  ∀ n γ (S : StorState → IProp GF) (i : Nat),
    nodeStorage (GF := GF) n γ S ∗ appliedLb n i ∗ storSnapLb n i ⊢
      AU <{ ∃∃ σ, S σ ∗ ⌜i ≤ σ.last ∧ i ≤ uint.nat σ.snap.index⌝ }> @ ⊤, ∅
        <{ S (σ.compact i), COMM True }>

/-- **Store a snapshot** at an applied index (a valid one: made with `snap_make`). -/
def stor_createSnapshot.spec : Prop :=
  ∀ n γ (S : StorState → IProp GF) (s : Snapshot),
    nodeStorage (GF := GF) n γ S ∗ appliedLb n (uint.nat s.index) ∗ snapValid γ s ⊢
      AU <{ ∃∃ σ, S σ ∗ ⌜uint.nat s.index ≤ σ.last ∧ σ.off ≤ uint.nat σ.snap.index ∧
              (σ.off ≤ uint.nat s.index → σ.termAt (uint.nat s.index) = some s.term)⌝ }>
          @ ⊤, ∅
        <{ S (σ.createSnapshot (uint.nat s.index) (some s.conf) s.data),
           COMM storSnapLb n (uint.nat s.index) }>

/-- **Read the attached storage** (etcd's `run` reads `Snapshot()` at its start; the examples'
`FirstIndex()` before a compaction and their status dumps): raft guarantees, at the read, that the
compaction point is at most the stored snapshot's index, that index at least a known lower bound,
and the stored snapshot empty or valid; it gives the new lower bound back. (Round 1, completeness F4;
round 2: the applied-index conjunct dropped, unused, and the shape of R3's `logStor_read`, from which
it is derived.) -/
def stor_read.spec : Prop :=
  ∀ n γ (S : StorState → IProp GF) (j : Nat),
    nodeStorage (GF := GF) n γ S ∗ storSnapLb n j ⊢
      AU <{ ∃∃ σ, S σ ∗ ⌜σ.off ≤ uint.nat σ.snap.index ∧ j ≤ uint.nat σ.snap.index⌝ ∗
              (⌜σ.snap.isEmpty⌝ ∨ snapValid γ σ.snap) }> @ ⊤, ∅
        <{ S σ, COMM storSnapLb n (uint.nat σ.snap.index) }>

/-- **Store a hard state**: raft reads it only at a start. -/
def stor_setHardState.spec : Prop :=
  ∀ n γ (S : StorState → IProp GF) (hs : HardState),
    nodeStorage (GF := GF) n γ S ⊢
      AU <{ ∃∃ σ, S σ }> @ ⊤, ∅ <{ S (σ.setHardState hs), COMM True }>

end laws

section golaws
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
  {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
  [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **raft's error values** (`init`'s `errors.New`s): fixed, non-nil, pairwise distinct. -/
def errs_init.spec : Prop :=
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ⊢
    ∃ (e1 e2 e3 e4 e5 e6 e7 e8 : GoInterface),
      errIs go_etcd_io.raft.v3.ErrStopped e1 ∗ errIs go_etcd_io.raft.v3.ErrProposalDropped e2 ∗
      errIs go_etcd_io.raft.v3.ErrCompacted e3 ∗ errIs go_etcd_io.raft.v3.ErrSnapOutOfDate e4 ∗
      errIs go_etcd_io.raft.v3.ErrUnavailable e5 ∗
      errIs go_etcd_io.raft.v3.ErrSnapshotTemporarilyUnavailable e6 ∗
      errIs go_etcd_io.raft.v3.ErrStepLocalMsg e7 ∗ errIs go_etcd_io.raft.v3.ErrStepPeerNotFound e8 ∗
      ⌜[e1, e2, e3, e4, e5, e6, e7, e8].Nodup ∧ interface.nil ∉ [e1, e2, e3, e4, e5, e6, e7, e8]⌝

def errIs_persistent.spec : Prop := ∀ g e, Persistent (errIs (GF := GF) g e)

def errIs_agree.spec : Prop :=
  ∀ g e1 e2, errIs (GF := GF) g e1 ∗ errIs g e2 ⊢ iprop(⌜e1 = e2⌝)

/-- **A `MemoryStorage` is a `Storage`**, its contents `memStor`, its initial configuration its
snapshot's. -/
def memStor_isStorage.spec : Prop :=
  ∀ (ms : Loc), ⊢ isStorage (GF := GF) (memStorIface ms) (memStor ms) (fun σ => σ.snap.conf)

/-- A `Status`'s progress map is the caller's (fresh copies, `Inflights` cloned; `nil` when the node
does not lead: `ownMap` of the empty map). (Round 1, completeness F5: etcd's `isLearnerReady` ranges
over it.) -/
def statusOwn_progress.spec : Prop :=
  ∀ (s : go_etcd_io.raft.v3.Status), statusOwn (GF := GF) s ⊢
    ∃ (pm : GMap w64 go_etcd_io.raft.v3.tracker.Progress),
      ownMap s.Progress' (DFrac.own 1) pm

/-- The bootstrap entries decode to their changes (raftpb's, 3h). -/
def bootEntryData_decode.spec : Prop :=
  ∀ (id : w64) (ctx : List w8), ctx ≠ [] →
    decodeConfChange EntryConfChange (bootEntryData id ctx) =
      some (.v1 ⟨ConfChangeAddNode, id, ctx, W64 0⟩)

def isStorage_persistent.spec : Prop := ∀ st S cf, Persistent (isStorage (GF := GF) st S cf)

def loggerOk_persistent.spec : Prop := ∀ lg, Persistent (loggerOk (GF := GF) lg)

/-- **Receiving from the `Ready` channel** (in a `select` or alone): with the driver token, the
receive's update (Perennial's channel `recvAu`) gives a `Ready` and what it holds. The run
goroutine never closes the channel. -/
def readyChan_recv.spec : Prop :=
  ∀ (n ch : Loc) γ (id : w64) (st : Driver)
    (Φ : go_etcd_io.raft.v3.Ready → Bool → IProp GF),
    isReadyChan n ch ∗ isNode n γ id ∗ nodeDriver n γ st ⊢
      ∃ (_ : Pos.Countable go_etcd_io.raft.v3.Ready) (γc : ChanNames),
        isChan ch γc go_etcd_io.raft.v3.Ready ∗
        (£ 1 ∗ £ 1 -∗ (▷ ∀ rd, readyGot n γ id st rd -∗ Φ rd true) -∗
          recvAu γc go_etcd_io.raft.v3.Ready Φ)

end golaws

end Raft
end EtcdGrove
end Perennial
