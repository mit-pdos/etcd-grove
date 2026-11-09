/-
# Raft's protocol-level model (batch R1): what a client of raft may know

The pure, transparent part of raft's node API (`Api.lean` has the resources and laws). Everything
here is a value a client of raft computes with or inspects: log entries, hard states,
configurations, snapshots, messages, the contents of a storage, the durable state a client keeps,
and what a `Ready` hands out. No resources, no theorems.

Shared with the raft core (R2), the log (R3), confchange/tracker (R4) and raftpb (3h): those
batches state their own specs over these values (`notes/specs-only/req/go_etcd_io_raft_v3*.md`).

**Indices.** Go keeps indices and terms as `uint64`; the model keeps them as `w64` where a Go value
carries them (an entry's term, a hard state, a snapshot's metadata, a message) and as `Nat` for
positions in the model's lists. A log is a list of entries from index 1: entry `i` is `l[i-1]`.

**Shared with raftpb and confchange** (integration I2). The message models (`LogEntry`,
`HardState`, `ConfState`, `Snapshot`, `ConfChangeV1`/`ConfChangeSingle`/`ConfChangeV2`/`ConfChangeI`,
`Msg`), raftpb's enumerations, the wire model (`decodeConfChange`, `bootEntryData`) are raftpb's
(`raftpb/Model.lean`, batch 3h), re-exported here under their old names (`Raft.LogEntry` is
`RaftPb.LogEntry`); the configuration (`Membership` with `simple`, `empty`, `ids`, `isJoint`,
`Valid`) is the tracker's (`tracker/Model.lean`, R4); what a change does (`Membership.applyChange`)
is defined from confchange's `changeV2` (`confchange/Model.lean`, R4). This module's own helpers
on raftpb's types (`LogEntry.isConfChange`, `isFiller`, `isEmptyV2`, `Snapshot.isEmpty`,
`ConfState.Is`) are declared in the `RaftPb` namespace, so that dot notation finds them on the
shared types.
-/
module

public import GeneratedProof.go_etcd_io.raft.v3
public import Spec.go_etcd_io.raft.v3.raftpb.Model
public import Spec.go_etcd_io.raft.v3.confchange.Model

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Raft

open Iris Iris.BI

/-! ## Enumerations (raftpb's values: `RaftPb.MsgHup`, ...) -/

export RaftPb (MsgHup MsgBeat MsgProp MsgApp MsgAppResp MsgVote MsgVoteResp MsgSnap MsgHeartbeat
  MsgHeartbeatResp MsgUnreachable MsgSnapStatus MsgCheckQuorum MsgTransferLeader MsgTimeoutNow
  MsgReadIndex MsgReadIndexResp MsgPreVote MsgPreVoteResp MsgStorageAppend MsgStorageAppendResp
  MsgStorageApply MsgStorageApplyResp MsgForgetLeader
  EntryNormal EntryConfChange EntryConfChangeV2
  ConfChangeAddNode ConfChangeRemoveNode ConfChangeUpdateNode ConfChangeAddLearnerNode
  ConfChangeTransitionAuto ConfChangeTransitionJointImplicit ConfChangeTransitionJointExplicit)

/-- The message types `IsLocalMsg` reports: generated and consumed inside a node, never sent. -/
def isLocalMsgType (t : w32) : Bool :=
  decide (t ∈ [MsgHup, MsgBeat, MsgUnreachable, MsgSnapStatus, MsgCheckQuorum, MsgStorageAppend,
    MsgStorageAppendResp, MsgStorageApply, MsgStorageApplyResp])

/-- The message types `IsResponseMsg` reports. -/
def isResponseMsgType (t : w32) : Bool :=
  decide (t ∈ [MsgAppResp, MsgVoteResp, MsgHeartbeatResp, MsgUnreachable, MsgReadIndexResp,
    MsgPreVoteResp, MsgStorageAppendResp, MsgStorageApplyResp])

/-- The ids `IsLocalMsgTarget` reports: raft's local append and apply threads
(`LocalAppendThread = ^uint64(0)`, `LocalApplyThread = ^uint64(0) - 1`). -/
def isLocalTarget (id : w64) : Bool :=
  decide (id ∈ [W64 (2 ^ 64 - 1), W64 (2 ^ 64 - 2)])

/-- `raft.StateType`'s values (a `SoftState`'s role). -/
def StateFollower : w64 := W64 0
def StateCandidate : w64 := W64 1
def StateLeader : w64 := W64 2
def StatePreCandidate : w64 := W64 3

/-- `raft.SnapshotStatus`'s values. -/
def SnapshotFinish : w64 := W64 1
def SnapshotFailure : w64 := W64 2

/-! ## Entries and logs -/

/- A log entry without its index (the index is its position in the log): raftpb's. -/
export RaftPb (LogEntry)

end Raft

/-! ### This module's helpers on raftpb's types (in `RaftPb`'s namespace, for dot notation) -/

namespace RaftPb

/-- A configuration-change entry (`EntryConfChange` or `EntryConfChangeV2`). -/
def LogEntry.isConfChange (e : LogEntry) : Prop :=
  e.type = EntryConfChange ∨ e.type = EntryConfChangeV2

/-- An empty normal entry: the one a new leader appends (and `Propose` of no data). -/
def LogEntry.isFiller (e : LogEntry) : Prop := e.data = [] ∧ e.type = EntryNormal

/-- An empty `EntryConfChangeV2`: the leave-joint entry raft appends itself (auto-leave). -/
def LogEntry.isEmptyV2 (e : LogEntry) : Prop := e.data = [] ∧ e.type = EntryConfChangeV2

instance (e : LogEntry) : Decidable e.isFiller := by unfold LogEntry.isFiller; infer_instance
instance (e : LogEntry) : Decidable e.isEmptyV2 := by unfold LogEntry.isEmptyV2; infer_instance
instance (e : LogEntry) : Decidable e.isConfChange := by unfold LogEntry.isConfChange; infer_instance

/-- The empty snapshot (`IsEmptySnap`: index `0`). -/
def Snapshot.isEmpty (s : Snapshot) : Prop := s.index = W64 0

/-- **A Go `ConfState` lists configuration `m`** (each list in any order, without repetition;
the auto-leave flag): confchange's `Lists` of its five fields. -/
def ConfState.Is (cs : ConfState) (m : Tracker.Membership) : Prop :=
  ConfChange.Lists cs.voters cs.learners cs.votersOutgoing cs.learnersNext cs.autoLeave m

end RaftPb

namespace Raft

/-- **The operations of a log**: the entries a client proposed, without the ones raft adds itself
(a leader's filler, the auto-leave entry). What `committedOps` tracks, so that a client's update
fires at its own entry and raft's own entries move nothing of the client's. -/
def opsOf (l : List LogEntry) : List LogEntry :=
  l.filter (fun e => !decide e.isFiller && !decide e.isEmptyV2)

/-- The term of index `i` of a log `l` (from index 1), `0` at index 0. -/
def termAt (l : List LogEntry) (i : Nat) : Option w64 :=
  if i = 0 then some (W64 0) else (l[i - 1]?).map (·.term)

/-! ## Hard state, configurations, snapshots -/

/-- An entry id: an index and its term. -/
structure EntryId where
  index : w64
  term : w64
deriving DecidableEq

/- `raftpb.HardState`, `ConfState` (the configuration as Go lists it), `Snapshot` (with its
metadata: the index and term of its last entry, its configuration and the application's data;
index `0` is the empty snapshot): raftpb's. -/
export RaftPb (HardState HardState.empty ConfState ConfState.empty Snapshot Snapshot.empty)

/- **A configuration** (a membership): the voters, the outgoing voters of a joint configuration,
the learners, the learners to be added when the joint configuration is left, and whether it is left
automatically; with `simple` (voters only), `empty`, `ids`, `isJoint` and `Valid` (**a
configuration raft accepts and reaches**): the tracker's (`Tracker.Membership`, R4). -/
export Tracker (Membership Membership.simple Membership.empty Membership.ids Membership.isJoint)

/-! ## Configuration changes -/

/- `raftpb.ConfChange` (the legacy change), `ConfChangeSingle`, `ConfChangeV2`, `ConfChangeI`
(either kind; `entryType`, `asV2`); **what the bytes of a conf-change entry of type `t` decode to**
(`decodeConfChange`: `proto.Unmarshal` into a `ConfChange` for `EntryConfChange`, a `ConfChangeV2`
for `EntryConfChangeV2`, `none` where it fails): raftpb's. -/
export RaftPb (ConfChangeV1 ConfChangeSingle ConfChangeV2 ConfChangeI decodeConfChange)

/-- **What `ApplyConfChange` of change `c` does to configuration `m`** (`c.AsV2()` run through
confchange's `Changer`, as `raft.applyConfChange` dispatches it: enter or leave a joint
configuration, or a simple change); `none` where it panics (removing every voter, a joint
transition from a joint configuration, an unknown transition or change type, ...:
`nonissues/raft-remove-last-voter-panic.md`, `raft-joint-empty-transition-panic.md`,
`raft-unknown-transition-panic.md`). Confchange's `changeV2` (R4; integration I2: was opaque). -/
def Membership.applyChange : ConfChangeI → Membership → Option Membership
  | .v1 cc, m => ConfChange.changeV2 ⟨ConfChange.TransitionAuto, [⟨cc.type, cc.nodeId⟩]⟩ m
  | .v2 c, m => ConfChange.changeV2 ⟨c.transition, c.changes⟩ m

/-- **A client's decision on a committed conf-change entry**: apply change `c` (the entry's own,
or another, as etcd applies `NodeID = 0` for a change it refuses: a no-op), or skip it (raft's
documented way of refusing: no `ApplyConfChange`). Every node decides the same for an entry
(`confDecided`). -/
inductive ConfDecision where
  | apply (c : ConfChangeI)
  | skip

/-- The configuration after a decision. -/
def ConfDecision.step : ConfDecision → Membership → Option Membership
  | .apply c, m => Membership.applyChange c m
  | .skip, m => some m

/-! ## Messages -/

/- **A raft message** (`raftpb.Message`), the protocol's content: what is on the wire between
nodes (raftpb's `Msg`; `Responses` is left out: only the local storage threads' messages carry any,
under `AsyncStorageWrites`, which no client enables; a stepped message's responses are ignored). -/
export RaftPb (Msg)

/-! ## Storage contents -/

/-- **The contents of a raft `Storage`** (a `MemoryStorage`'s, field by field): the index and term
of the entry before the stored ones (`off`, `offTerm`: the compaction point; `ents[0]`, the dummy,
in Go), the entries after it, the latest snapshot and the hard state. A `Storage` implementation
other than `MemoryStorage` presents its contents as this record (`isStorage`). -/
structure StorState where
  off : Nat
  offTerm : w64
  ents : List LogEntry
  snap : Snapshot
  hs : HardState

/-- `NewMemoryStorage`'s contents. -/
def StorState.empty : StorState := ⟨0, W64 0, [], Snapshot.empty, HardState.empty⟩

def StorState.last (σ : StorState) : Nat := σ.off + σ.ents.length
def StorState.first (σ : StorState) : Nat := σ.off + 1

/-- The term of index `i`, if the storage has it (`Term`; the compaction point's included). -/
def StorState.termAt (σ : StorState) (i : Nat) : Option w64 :=
  if i = σ.off then some σ.offTerm
  else if σ.off < i then (σ.ents[i - σ.off - 1]?).map (·.term) else none

/-- **`Append(es)`, `es` at indices `k, k+1, ...`**: entries at or below the compaction point are
dropped, the stored entries from the first new index on are replaced. `none` where Go panics: a
gap after the last stored entry. -/
def StorState.append (σ : StorState) (k : Nat) (es : List LogEntry) : Option StorState :=
  if es = [] ∨ k + es.length ≤ σ.first then some σ
  else
    let k' := max k σ.first
    let es' := es.drop (k' - k)
    if k' ≤ σ.last + 1 then some { σ with ents := σ.ents.take (k' - σ.first) ++ es' }
    else none

/-- **`ApplySnapshot(s)`**: the storage becomes the snapshot (its log empty after it); unchanged,
with `ErrSnapOutOfDate`, if it holds a non-empty snapshot at least as new. -/
def StorState.applySnapshot (σ : StorState) (s : Snapshot) : StorState :=
  if σ.snap.index ≠ W64 0 ∧ uint.nat s.index ≤ uint.nat σ.snap.index then σ
  else { σ with snap := s, off := uint.nat s.index, offTerm := s.term, ents := [] }

def StorState.applySnapshotErr (σ : StorState) (s : Snapshot) : Bool :=
  σ.snap.index ≠ W64 0 ∧ uint.nat s.index ≤ uint.nat σ.snap.index

/-- **`CreateSnapshot(i, cs, data)`**: the snapshot at `i`, of the stored term at `i`, of the
configuration `cs` (the stored snapshot's if `cs` is `nil`: `none`) and `data`; unchanged, with
`ErrSnapOutOfDate`, at or below the stored snapshot. Go panics past the last index, and at an index
compacted past the snapshot (`CreateSnapshot.spec`'s premise). -/
def StorState.createSnapshot (σ : StorState) (i : Nat) (cs : Option ConfState) (data : List w8) :
    StorState :=
  if i ≤ uint.nat σ.snap.index then σ
  else { σ with snap := ⟨W64 i, (σ.termAt i).getD (W64 0), cs.getD σ.snap.conf, data⟩ }

/-- **`Compact(i)`**: the entries up to `i` dropped (`i` the new compaction point); unchanged, with
`ErrCompacted`, at or below the compaction point. Go panics past the last index. -/
def StorState.compact (σ : StorState) (i : Nat) : StorState :=
  if i ≤ σ.off then σ
  else { σ with off := i, offTerm := (σ.termAt i).getD (W64 0), ents := σ.ents.drop (i - σ.off) }

def StorState.setHardState (σ : StorState) (hs : HardState) : StorState := { σ with hs := hs }

/-! ## The client's durable state -/

/-- **A node's durable state** (`raftState`): what raft needs to find again after a restart, and
nothing volatile -- its term and vote, the commit index of the last batch it entered and of the
last one that wrote entries or a snapshot (`wcommit`: the lowest commit a restart may present,
`StorageHolds`), and its log from a base entry (the latest snapshot's, or index 0). -/
structure Durable where
  term : w64
  vote : w64
  commit : w64
  wcommit : w64
  base : EntryId
  ents : List LogEntry

/-- A node that has stored nothing. -/
def Durable.init : Durable := ⟨W64 0, W64 0, W64 0, W64 0, ⟨W64 0, W64 0⟩, []⟩

def Durable.last (D : Durable) : Nat := uint.nat D.base.index + D.ents.length

/-- The term of index `i` in the durable log (the base's included). -/
def Durable.termAt (D : Durable) (i : Nat) : Option w64 :=
  if i = uint.nat D.base.index then some D.base.term
  else if uint.nat D.base.index < i then (D.ents[i - uint.nat D.base.index - 1]?).map (·.term)
  else none

/-- **A storage holds a durable state**: what a restart from that storage needs of it. The term and
vote are the durable ones; the stored log is the durable log from the stored compaction point (at
or above the durable base; below it only if the storage holds a snapshot there); the stored commit
is at least the durable `wcommit`, at most the durable commit, and covers the compaction point and
the stored snapshot. -/
def StorageHolds (D : Durable) (σ : StorState) : Prop :=
  uint.nat D.base.index ≤ σ.off ∧
  D.termAt σ.off = some σ.offTerm ∧
  σ.ents = D.ents.drop (σ.off - uint.nat D.base.index) ∧
  σ.hs.term = D.term ∧ σ.hs.vote = D.vote ∧
  uint.nat D.wcommit ≤ uint.nat σ.hs.commit ∧ uint.nat σ.hs.commit ≤ uint.nat D.commit ∧
  σ.off ≤ uint.nat σ.hs.commit ∧
  σ.off ≤ uint.nat σ.snap.index ∧ uint.nat σ.snap.index ≤ uint.nat σ.hs.commit ∧
  (σ.snap.isEmpty → σ.off = uint.nat D.base.index)

/-! ## What a `Ready` hands out -/

/-- **A `Ready`'s contents** (`raft.Ready`), as values: the soft state if it changed (leader,
role), the hard state if it changed, the read states (context, index), the entries to store and the
index of the first, the snapshot to store and install, the committed entries to apply, the messages
to send, and `MustSync`. -/
structure Batch where
  soft : Option (w64 × w64)
  hs : Option HardState
  reads : List (List w8 × w64)
  entsFrom : Nat
  ents : List LogEntry
  snap : Option Snapshot
  committed : List LogEntry
  msgs : List Msg
  mustSync : Bool

/-- The durable state after a batch: its hard state, its snapshot (the log restarts at it), its
entries (the log cut at the first new index). `wcommit` moves only with a batch that writes entries
or a snapshot. -/
def Durable.next (D : Durable) (b : Batch) : Durable :=
  let hs := b.hs.getD ⟨D.term, D.vote, D.commit⟩
  let D1 : Durable := match b.snap with
    | some s => { D with base := ⟨s.index, s.term⟩, ents := [] }
    | none => D
  let D2 : Durable :=
    if b.ents = [] then D1
    else { D1 with ents := D1.ents.take (b.entsFrom - uint.nat D1.base.index - 1) ++ b.ents }
  { D2 with term := hs.term, vote := hs.vote, commit := hs.commit,
            wcommit := if b.ents = [] ∧ b.snap = none then D.wcommit else hs.commit }

/-- **The durable state a crash during a batch's write can leave** (round 3, 2e's request): `D` with
the first `j` of the batch's entries written (the log cut at the batch's first index; nothing
written if `j = 0`), and hard state `hs` -- the old one or the batch's, with a commit index in
between (a commit-only state record lost). The stored commit is then the whole truth
(`wcommit := hs.commit`). This is the no-snapshot case; a batch with a snapshot is covered when
nothing or all of it is written (`Durable.crashOk`, `Api.lean`, with `raftState_crash.spec`: for a
batch with no snapshot `crashOk` is this relation). Changes: repair3-boot, the crash pass's request
(the docstring said snapshot batches were not covered). -/
def Durable.crashed (D : Durable) (b : Batch) (j : Nat) (hs : HardState) : Durable :=
  let es := b.ents.take j
  let D1 : Durable :=
    if es = [] then D
    else { D with ents := D.ents.take (b.entsFrom - uint.nat D.base.index - 1) ++ es }
  { D1 with term := hs.term, vote := hs.vote, commit := hs.commit, wcommit := hs.commit }

/-- **At most one conf-change entry above the commit** of a durable state (raft's `ConfI1` at the
cut): what makes a restart from it safe. A node whose stored log holds two configuration changes
above its stored commit restarts at a configuration older than its committed log, with a commit too
low for raft's campaign guard to see the pending change, and can win an election counted in that
older configuration, after which two nodes commit different entries at one index. **A real raft bug**
(`issues/raft-commit-lost-with-entries-kept.md`: reproduced by a Go test against the pinned raft,
etcd's PreVote and CheckQuorum on), not only a gap in the proof: this condition is the premise under
which a crash restart is safe, and a client whose storage can leave the entries of a `Ready` without
its `HardState` (etcd's WAL: entry records, then the state record, one fsync) must establish it or
stay outside the covered executions. -/
def Durable.confAboveOk (D : Durable) : Prop :=
  ((D.ents.zipIdx (uint.nat D.base.index + 1)).filter
    (fun p => uint.nat D.commit < p.2 ∧ p.1.isConfChange)).length ≤ 1

/-- **What a client knows of the `Ready` loop's position** (`nodeDriver`): the committed log handed
out so far from index 1 (`delivered`: every `Ready`'s `CommittedEntries` in order, a snapshot's
prefix in place of the entries it covers, after the prefix the node started at), the last hard state
handed out (the `prevst` of `MustSync`), the durable state of the last batch entered, and the last
role reported in a `SoftState`, and the snapshot of the batch entered and not yet `Advance`d
(`Advance` moves the node's configuration view to it). -/
structure Driver where
  delivered : List LogEntry
  hs : HardState
  durable : Durable
  role : w64
  lastSnap : Option Snapshot

/-- The driver after a batch is entered: `dl` is the delivered log after it (the old one with the
batch's committed entries, or the snapshot's prefix). -/
def Driver.after (st : Driver) (b : Batch) (dl : List LogEntry) : Driver :=
  { delivered := dl, hs := b.hs.getD st.hs, durable := st.durable.next b,
    role := (b.soft.map (·.2)).getD st.role, lastSnap := b.snap }

/-- The driver a node starts with, at delivered log `l` and stored hard state `hs`. -/
def Driver.start (l : List LogEntry) (hs : HardState) (D : Durable) : Driver :=
  ⟨l, hs, D, StateFollower, none⟩

/-- **The facts a `Ready` states of its batch**, given the driver `st` it was handed out from: the
committed entries follow the delivered ones; the new commit index covers them and lies within the
durable log after the batch; the entries to store start after the old commit and at most one past
the durable log, or, with a snapshot, at most one past the snapshot (verify-round, A4 P1: a lagging
follower restores a snapshot far past its durable log and appends the next leader's entries after it
before the `Ready` is taken, `unstable.restore` setting `offset = s.index + 1`); with a snapshot, no committed entries, and the snapshot past the delivered log and
within the commit; `MustSync` as `MustSync` computes it; every entry of one of raft's types; and
(integration I2, 2d's request) every committed entry and the snapshot of the batch have a term at most
the batch's hard-state term as the driver knows it after the batch (raft's log terms never exceed its
current term, and a `Ready` reports a changed term in its `HardState`: etcd's merged-snapshot guard
`m.GetTerm() == raftTerm` rests on it). -/
def BatchOk (st : Driver) (b : Batch) : Prop :=
  let hs' := b.hs.getD st.hs
  (b.hs = none ∨ b.hs ≠ some st.hs) ∧
  uint.nat st.hs.commit ≤ uint.nat hs'.commit ∧
  uint.nat hs'.commit ≤ (st.durable.next b).last ∧
  (b.ents ≠ [] → uint.nat st.hs.commit < b.entsFrom ∧
    b.entsFrom ≤ (match b.snap with | some s => uint.nat s.index | none => st.durable.last) + 1) ∧
  (∀ e ∈ b.ents, uint.nat e.type ≤ 2) ∧
  b.mustSync = (b.ents ≠ [] ∨ hs'.term ≠ st.hs.term ∨ hs'.vote ≠ st.hs.vote) ∧
  (∀ e ∈ b.committed, uint.nat e.term ≤ uint.nat hs'.term) ∧
  (∀ s, b.snap = some s → uint.nat s.term ≤ uint.nat hs'.term) ∧
  match b.snap with
  | none => (st.delivered ++ b.committed).length ≤ uint.nat hs'.commit
  | some s => b.committed = [] ∧ st.delivered.length < uint.nat s.index ∧
      uint.nat s.index ≤ uint.nat hs'.commit

/-- The delivered log after a batch whose snapshot (if any) has prefix `sl` (the committed log up to
the snapshot's index). -/
def deliveredAfter (st : Driver) (b : Batch) (sl : List LogEntry) : List LogEntry :=
  match b.snap with
  | none => st.delivered ++ b.committed
  | some _ => sl

/-- **A node's configuration view** (`nodeConf`): the configuration its tracker holds, after the
first `applied` entries of the committed log. -/
structure ConfView where
  applied : Nat
  membership : Membership

/- **The bytes of a bootstrap entry** for peer `id` with context `ctx`: what `proto.Marshal`
gives the `ConfChange{Type: AddNode, NodeId: id, Context: ctx}` that `RawNode.Bootstrap` builds
(raftpb's `bootEntryData`, with `RaftPb.bootCC_facts`: it encodes that change, so
`decodeConfChange EntryConfChange (bootEntryData id ctx) = some (.v1 ⟨AddNode, id, ctx, 0⟩)` for a
non-empty `ctx`: `Api.lean`'s `bootEntryData_decode`). -/
export RaftPb (bootEntryData)

/-- **The bootstrap log of peers `ps`** (`StartNode`'s, `RawNode.Bootstrap`'s): a legacy `AddNode`
of each peer, with its context (non-empty: a `nil` and an empty context marshal differently; etcd's
are JSON), at term 1, the bytes Go's marshalling gives. -/
def BootLog (ps : List (w64 × List w8)) (boot : List LogEntry) : Prop :=
  boot.length = ps.length ∧
  (∀ p ∈ ps, p.2 ≠ []) ∧
  ∀ (k : Nat) (e : LogEntry), boot[k]? = some e → ∃ p : w64 × List w8, ps[k]? = some p ∧
    e = ⟨W64 1, EntryConfChange, bootEntryData p.1 p.2⟩

end Raft
end EtcdGrove
end Perennial
