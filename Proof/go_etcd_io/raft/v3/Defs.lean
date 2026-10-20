/-
Port of `election_proof/defs.v` (at 857d09190): shared vocabulary for the election
proof.

Lean notes:
* The Rocq records `logstate.t`, `nstate.t`, `inflights.t`, `progress.t`, `trk.t`
  and the inductives `prole.t`, `prstate.t` are `LogState`, `NState`, `Inflights`,
  `Progress`, `Trk`, `PRole`, `PRState` (in namespace `Perennial.EtcdGrove`, so
  distinct from the Goose types `tracker.Inflights` and `tracker.Progress`); fields
  are lowerCamel (`sent_commit` → `sentCommit`, `max_bytes` → `maxBytes`).
  Constructors are lowerCamel (`prole.PreCandidate` → `PRole.preCandidate`).
* The Rocq tactics `w32_ne`, `intros_ambient` and `logstate_simpl` have no
  counterpart (`decide`, the section variables and `simp only [...]` do their jobs).
* stdpp's `map_imap` has no counterpart on `GMap`; `GMap.imap` below is the one this
  file needs (with `GMap.lookup_imap`).
* Lemma names keep the lowerCamel definition name the old port used
  (`nstateWf_becomeFollower`, `toPState_sendMsgs`, `replSends_prvals`).

**Shared vocabulary for the Raft proof**
-/
module

public import Proof.go_etcd_io.raft.v3.Base
public import Proof.go_etcd_io.raft.v3.Protocol

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial

/-- stdpp's `map_imap`: a map whose value at `k` is `f k v`, where the map has `v`. -/
def GMap.imap {K : Type _} {V V' : Type _} [DecidableEq K] (f : K → V → Option V')
    (m : GMap K V) : GMap K V' :=
  ⟨fun k => (m.lookup k).bind (f k),
   by
    obtain ⟨l, hl⟩ := m.finite
    refine ⟨l, fun k h => hl k ?_⟩
    cases e : m.lookup k <;> simp_all⟩

theorem GMap.lookup_imap {K : Type _} {V V' : Type _} [DecidableEq K]
    (f : K → V → Option V') (m : GMap K V) (k : K) :
    (GMap.imap f m) !! k = (m !! k).bind (f k) := rfl

namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-! ## Physical roles (2026-10-04, pre-vote)

`r.state` has four values; the protocol's `Role` (`Protocol/Model.lean`) has three.
`preCandidate` (`StatePreCandidate`, `becomePreCandidate`) is an implementation detail
of pre-vote: protocol-wise a pre-candidate is a follower with no leader and an empty
tally (`toPState` below; notes/raft-replication-model.md, "Phase 3 ... Pre-vote"). -/

inductive PRole where
  | follower | candidate | leader | preCandidate
  deriving DecidableEq, Inhabited

/-- The protocol reading of a physical role. -/
def proleRole : PRole → Role
  | .follower | .preCandidate => .follower
  | .candidate => .candidate
  | .leader => .leader

theorem proleRole_leader (ro : PRole) : proleRole ro = .leader ↔ ro = .leader := by
  cases ro <;> simp [proleRole]

theorem proleRole_candidate (ro : PRole) : proleRole ro = .candidate ↔ ro = .candidate := by
  cases ro <;> simp [proleRole]

theorem proleRole_follower (ro : PRole) :
    proleRole ro = .follower ↔ ro = .follower ∨ ro = .preCandidate := by
  cases ro <;> simp [proleRole]

theorem proleRole_not_leader (ro : PRole) (Hne : ro ≠ .leader) : proleRole ro ≠ .leader :=
  fun Hr => Hne ((proleRole_leader ro).1 Hr)

/-! ## Message-type constants, as Lean values

`raftpb.MessageType` is a `w32`; the Goose constants are opaque `val`s, so we name the
underlying numbers (`raftpb.v:74-120`). -/

def MsgHup : w32 := W32 0
def MsgProp : w32 := W32 2
def MsgApp : w32 := W32 3
def MsgAppResp : w32 := W32 4
def MsgVote : w32 := W32 5
def MsgVoteResp : w32 := W32 6
def MsgSnap : w32 := W32 7
def MsgHeartbeat : w32 := W32 8
def MsgHeartbeatResp : w32 := W32 9
def MsgReadIndex : w32 := W32 15
def MsgReadIndexResp : w32 := W32 16
def MsgPreVote : w32 := W32 17
def MsgPreVoteResp : w32 := W32 18
def MsgStorageAppendResp : w32 := W32 20
-- (2026-10-13) the local reports, leader transfer and `ForgetLeader`
def MsgUnreachable : w32 := W32 10
def MsgSnapStatus : w32 := W32 11
-- (2026-10-17) `CheckQuorum` on: the leader's quorum check, which `tickHeartbeat` steps
def MsgCheckQuorum : w32 := W32 12
def MsgTransferLeader : w32 := W32 13
def MsgTimeoutNow : w32 := W32 14
def MsgForgetLeader : w32 := W32 23

def StateFollower : w64 := W64 0
def StateCandidate : w64 := W64 1
def StateLeader : w64 := W64 2
def StatePreCandidate : w64 := W64 3

section consts
variable [FfiSyntax]

def campaignElection : CampaignType := go!"CampaignElection"
def campaignPreElection : CampaignType := go!"CampaignPreElection"
def campaignTransfer : CampaignType := go!"CampaignTransfer"

end consts

/-- The `Context` of `campaign(t)`'s vote requests (2026-10-13): the leader-transfer
marker for a transfer's campaign (`[]byte(t)`), nothing otherwise. -/
def transferCtx [FfiSyntax] (t : CampaignType) : List w8 :=
  if t = campaignTransfer then campaignTransfer else []

def VotePending : w8 := W8 1
def VoteLost : w8 := W8 2
def VoteWon : w8 := W8 3

def stateW64 : PRole → w64
  | .follower => StateFollower
  | .candidate => StateCandidate
  | .leader => StateLeader
  | .preCandidate => StatePreCandidate

/-! ## Abstraction of physical messages

Every message type raft sends between nodes has an abstraction (`MsgType`); the local
ones (`MsgHup`, `MsgBeat`, `MsgStorage*`, `MsgCheckQuorum`, ...) do not, and
`ownRaftPhys` lets them drop out of the abstract outbox. (Until 2026-10-01 only the
four election types had one, and `MsgAppResp` -- which `appendEntry` queues -- dropped
out too.) -/

def mtypeOf (t : w32) : Option MsgType :=
  match uint.Z t with
  | 2 => some .propose
  | 3 => some .app
  | 4 => some .appResp
  | 5 => some .vote
  | 6 => some .voteResp
  | 7 => some .snap
  | 8 => some .heartbeat
  | 9 => some .heartbeatResp
  | 15 => some .readIndex
  | 16 => some .readIndexResp
  | 17 => some .preVote
  | 18 => some .preVoteResp
  | _ => none

theorem mtypeOf_MsgVote : mtypeOf MsgVote = some .vote := rfl
theorem mtypeOf_MsgVoteResp : mtypeOf MsgVoteResp = some .voteResp := rfl
theorem mtypeOf_MsgApp : mtypeOf MsgApp = some .app := rfl
theorem mtypeOf_MsgAppResp : mtypeOf MsgAppResp = some .appResp := rfl
theorem mtypeOf_MsgHeartbeat : mtypeOf MsgHeartbeat = some .heartbeat := rfl
theorem mtypeOf_MsgHeartbeatResp : mtypeOf MsgHeartbeatResp = some .heartbeatResp := rfl
theorem mtypeOf_MsgSnap : mtypeOf MsgSnap = some .snap := rfl
theorem mtypeOf_MsgProp : mtypeOf MsgProp = some .propose := rfl
theorem mtypeOf_MsgPreVote : mtypeOf MsgPreVote = some .preVote := rfl
theorem mtypeOf_MsgPreVoteResp : mtypeOf MsgPreVoteResp = some .preVoteResp := rfl

/-- Only `MsgSnap` is abstracted as a `snap`. -/
theorem mtypeOf_Snap (t : w32) (H : mtypeOf t = some .snap) : t = MsgSnap := by
  unfold mtypeOf at H
  split at H <;> simp_all
  rename_i h
  exact uint_Z_inj.1 (by rw [h]; rfl)

/-- A message type the model does not describe is none of the ones it does. -/
theorem mtypeOf_None_ne (t : w32) (Hn : mtypeOf t = none) :
    t ≠ MsgProp ∧ t ≠ MsgApp ∧ t ≠ MsgAppResp ∧ t ≠ MsgVote ∧ t ≠ MsgVoteResp ∧
    t ≠ MsgSnap ∧ t ≠ MsgHeartbeat ∧ t ≠ MsgHeartbeatResp ∧ t ≠ MsgReadIndex ∧
    t ≠ MsgReadIndexResp ∧ t ≠ MsgPreVote ∧ t ≠ MsgPreVoteResp := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rintro rfl; exact absurd Hn (by decide))

section msgs
variable [FfiSyntax]

/-- The abstraction of a physical message `m` whose `Entries` slice holds `ents`, with
the sender and term given separately: `send` stamps both (`From := r.id` when unset,
`Term := r.Term` for most types), so what reaches the queue is `m` with those two
fields replaced. -/
def absMsgFrom (ty : MsgType) (m : MessageM) (src term : w64)
    (ents : List EntryM) (ctx : List w8 := []) : Msg :=
  Msg.mkV ty src m.To' term m.Reject' m.Index' m.LogTerm' m.Commit' m.RejectHint' ents [] ctx

/-- The abstraction of a physical message. Not a function of `m` alone: `m.Entries` is
a slice, and `ents` is the list it points to -- `ownRaftPhys` holds `m.Entries ↦*□ ents`
for every queued message (`outboxRel`, `InvRaftPhys.lean`). Not for a `MsgSnap`: see
`absSnap`. -/
def absMsg (ty : MsgType) (m : MessageM) (ents : List EntryM)
    (ctx : List w8 := []) : Msg :=
  absMsgFrom ty m m.From' m.Term' ents ctx

-- (D22 S-b′, 2026-10-20) `CSLists` is `Protocol/Model.lean`'s (a `Msg` field)

-- (D22 S-b′3, 2026-10-20) `SnapTrip` and `msgSnapTrip` are `Protocol/Model.lean`'s

/-- The abstraction of a `MsgSnap` (2026-10-02). What the protocol reads of a snapshot
is behind the pointer `m.Snapshot`: `sv` is the `Snapshot` it points to (since the raft v3.7
retarget, stage R1, its record `SnapshotM`), and `voters`
the lists behind `sv`'s `Metadata.ConfState` slices (since 2026-10-14, stage B8, all four;
the abstract message kept the incoming voters until D22 S-b′, 2026-10-20: now all four and the
`AutoLeave`, which the message's certificate is about). `index`/`logterm` are the
snapshot's `Metadata.Index`/`Metadata.Term` -- not `m`'s own `Index`/`LogTerm`, which
`maybeSendSnapshot` leaves at `0` -- and there are no entries. As for `absMsgFrom`,
`src`/`term` are given separately because `send` stamps them. -/
def absSnapFrom (m : MessageM) (src term : w64) (sv : SnapshotM)
    (voters : CSLists) : Msg :=
  Msg.mkS .snap src m.To' term m.Reject' sv.Metadata'.Index' sv.Metadata'.Term'
    m.Commit' m.RejectHint' [] voters sv.Metadata'.ConfState'.AutoLeave' []

def absSnap (m : MessageM) (sv : SnapshotM) (voters : CSLists) : Msg :=
  absSnapFrom m m.From' m.Term' sv voters

end msgs

section msgs_ghost
variable [FfiSyntax] {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF]

/-- What a message other than a heartbeat or its response carries as a protocol message
does not depend on its `Context` (2026-10-12; a heartbeat's is a read-index position): the
branches that do not echo it work at the abstraction with none. -/
theorem isMessage_absMsg_ctx (γ : RaftNames) (ty : MsgType) (m : MessageM)
    (ents : List EntryM) (ctx : List w8)
    (hty : ty ≠ .heartbeat ∧ ty ≠ .heartbeatResp) :
    isMessage (GF := GF) γ (absMsg ty m ents ctx) = isMessage γ (absMsg ty m ents) := by
  obtain ⟨h1, h2⟩ := hty
  cases ty <;> first | contradiction | rfl

theorem isMessage_ctx_intro (γ : RaftNames) (ty : MsgType) (m : MessageM)
    (ents : List EntryM) (ctx : List w8)
    (hty : ty ≠ .heartbeat ∧ ty ≠ .heartbeatResp) :
    isMessage (GF := GF) γ (absMsg ty m ents) ⊢ isMessage γ (absMsg ty m ents ctx) := by
  rw [isMessage_absMsg_ctx γ ty m ents ctx hty]

end msgs_ghost

/-! ## The abstract state of a `raftLog`

What every `raftLog` spec is stated at.
* `prev`, `sents`, `uents`: the entry list, as described above.
* `committed`, `applied`: `l.committed` and `l.applied`. Nothing on the election path
  writes them; they are in the state because `hasUnappliedConfChanges` and
  `maybeSendAppend` read them and a spec has to be able to say what was read.

Every field is physical. Until 2026-09-29 there was a sixth, `page`: a slice
`raftLog.slice` had handed out while sharing memory with the log, on loan, with a wand
back in `ownRaftLog`. It went when the log started holding its entries read-only
(`↦*□`, `InvRaftlog.lean`): a slice `slice` returns is then the caller's for good, and
there is no loan to record.

(Until 2026-09-23 the log had three shapes: `own_raftLog_at l prev sents uents`, the
existential `own_raftLog l`, and the "page out" shape that `slice`/`entries` returned
as `l ↦ lv ∗ s ↦*{dq} es ∗ (l ↦ lv -∗ s ↦*{dq} es -∗ own_raftLog_at …)`.
notes/decisions.md, "One predicate per object".) -/

structure LogState [FfiSyntax] where
  prev : entryID
  sents : List EntryM
  uents : List EntryM
  committed : w64
  applied : w64
  /-- the pending, not yet stored snapshot's id (`unstable.snapshot`, set by
  `raftLog.restore`); `none` when there is none. Added 2026-10-02 with `MsgSnap`: with
  a snapshot pending, `prev` is its id and `sents = []` (`InvRaftlog.lean`,
  `LogStoreOk`). -/
  snap : Option entryID
  /-- `unstable.offsetInProgress` (2026-10-05, for `Ready`): the unstable entries below
  it have been handed to the application by a `Ready` (`acceptUnstable`);
  `nextUnstableEnts` is the rest. Between `unstable.offset` and the end of the log
  (`InvRaftlog.lean`, `Hipb`). -/
  inprogress : w64
  /-- `l.applying` (2026-10-05): the last index handed to the application for applying
  (`acceptApplying`); `nextCommittedEnts` starts after it.
  `applied <= applying <= committed`. -/
  applying : w64
  /-- The entries the last `Ready` handed out (`Ready.Entries`) that the application
  has **not yet appended to the `Storage`** (2026-10-05); `[]` when there are none.
  This is the storage handshake, recorded as a field of the log's state ("a loan is a
  field of the state", notes/decisions.md): `ownRaftLog` still owns the `Storage` --
  `Step` reads it on most paths, so it cannot be lent out -- and promises that once
  the storage also holds these entries, the in-progress prefix of the log is persisted
  (`InvRaftlog.lean`, `Hpersist`, `StorApp`). Since 2026-10-10 they are also the
  storage's pending batch (`StorState.pend`, `PendLogOk`): `acceptUnstable` hands out
  the right to append them, and `ownRaftLog_absorb` takes the receipt back and empties
  the field (until then `ownRaftLog_persist` lent the storage itself); `Advance`
  requires it empty. -/
  unpersisted : List EntryM
  /-- What the `Storage` holds (its entries after `prev`) once the application has
  appended `unpersisted` (2026-10-10), while no snapshot is pending (`InvRaftlog.lean`,
  `Hstored`): ghost, not a Go field. Only a `Ready` changes it (`logAcceptUnstable`: the
  whole log, which the storage holds once the entries handed out are appended); a
  truncating `MsgApp` leaves it, so after one the storage may hold entries the log no
  longer has. `stableTo` needs it (`StableOk`, `InvReadylog.lean`): an acknowledgement
  `Advance` steps after a truncation is right only because the storage still agrees
  with the log up to the acknowledged entry. -/
  stored : List EntryM
  /-- `l.applyingEntsSize` and `l.maxApplyingEntsSize` (2026-10-05): the flow control
  on handing out committed entries. In the state because `acceptApplying` calls
  `maxAppliableIndex` between updating the size and the paused flag, and only what the
  state records survives that call (`ownRaftLog`'s `Hpaused` needs the size to be
  under the limit while applying is not paused). -/
  apsize : w64
  apmax : w64
  /-- `l.storage`, the `Storage` interface value the log reads (2026-10-10). Constant:
  nothing writes the field after `newLogWithSize`. In the state so that a client can
  name the storage it appends to (`RNState.storage`): the receipt of an append
  (`appendedTok st σ p`, `InvStorage.lean`) is for one storage, and only the log that
  reads that storage may absorb it (`ownRaftLog_absorb`). -/
  storage : Storage
  /-- The snapshots the node may send (2026-10-15, stage S): ghost, not a Go field. The
  `Storage`'s snapshot (once it is not the empty one) and every snapshot the log restored are
  in it (`ownRaftLog`'s `Hsksn`, `Hpksn`), so `raftLog.snapshot` returns one of them. Only a
  restore (`logRestore`) adds to it. The protocol does not read it (`toPState`). -/
  ksn : List SnapTrip
  /-- (D19i part 1, 2026-10-18) The floor raft has published to the application
  (`StorState.fl`, `InvStorage.lean`): the storage may be compacted, and its snapshot replaced,
  up to it. Ghost, not a Go field. At most `applied` (`ownRaftLog`'s `Hfl`): raft's
  `hasUnappliedConfChanges` reads the log from `applied + 1`. -/
  fl : w64 := 0
  /-- (D22 S-d1, 2026-10-20) `unstable.snapshotInProgress`: the pending snapshot has been handed
  to the application by a `Ready` (`acceptInProgress`), so `nextSnapshot` no longer returns it.
  `false` with no snapshot pending (`ownRaftLog`'s `Hsipn`); `restore` clears it. -/
  sip : Bool := false

/-! ## The tracker's records (2026-10-02)

The public representation predicates of the tracker side -- `ownInflights l i`,
`ownProgress pr p` and `ownTracker cfg tv t` (`InvTracker.lean`) -- are indexed by
these records rather than by the Goose struct types: each holds exactly the state the
exported methods' specs need (notes/raft-replication-model.md, "Public representation
predicates"). They live here and not in `InvTracker.lean` because `NState.prvals`
below is a map of `Progress`, and `InvTracker.lean` builds on this file -- the same
reason `LogState` is here. -/


/-- An `Inflights` window, as its methods' callers see it: how many messages and bytes
are in flight, and the two limits. The ring buffer (`start`, `buffer` and its
contents) is internal to `Inflights` (`ownInflightsRaw`, `InvTracker.lean`). `count`
and `size` are Go `int`s, `bytes` and `maxBytes` `uint64`s; all four as the integers
they denote. -/
structure Inflights where
  count : Int
  size : Int
  bytes : Int
  maxBytes : Int

/-- `StateType`, as an inductive: `StateProbe`/`StateReplicate`/`StateSnapshot` =
`0`/`1`/`2` (new/code/go_etcd_io/raft/v3/tracker.v:47-51). No other value is reachable
-- `Progress.IsPaused` panics on one. -/
inductive PRState where
  | probe | replicate | snapshot
  deriving DecidableEq, Inhabited

/-- A `Progress`, with the state an inductive. `learner` is `IsLearner` (since 2026-10-13,
reconfiguration stage L; until then the abstraction function below was undefined on a
learner). `paused` is
`MsgAppFlowPaused`; `infl` is the window `Inflights` points at. `RecentActive` is not in
it: no spec states it (checkQuorum, which reads it, is out of scope; `maybeSendSnapshot`
reads the Go field and case-splits on it). Until 2026-10-08 it was a field. -/
structure Progress where
  matched : w64
  next : w64
  sentCommit : w64
  state : PRState
  pendingSnapshot : w64
  paused : Bool
  infl : Inflights
  learner : Bool

/-- The tracker, as `ownTracker` is indexed by it: the vote tally, the progress map (id
to `*Progress` -- physical state, like `NState.log`, because callers hold a raw
`*Progress` across calls) and each peer's `Progress`. (`tracker` is the Goose module's
name.) -/
structure Trk where
  votes : GMap w64 Bool
  prs : GMap w64 Loc
  peers : GMap w64 Progress

/-! ### Abstraction functions -/

def prstateW64 : PRState → w64
  | .probe => W64 0
  | .replicate => W64 1
  | .snapshot => W64 2

def prstateOfW64 (st : w64) : Option PRState :=
  if st = W64 0 then some .probe
  else if st = W64 1 then some .replicate
  else if st = W64 2 then some .snapshot
  else none

theorem prstateOfW64_Some (st : w64) (p : PRState) :
    prstateOfW64 st = some p ↔ st = prstateW64 p := by
  unfold prstateOfW64
  constructor
  · intro Hp
    split at Hp
    · cases Hp; simp_all [prstateW64]
    split at Hp
    · cases Hp; simp_all [prstateW64]
    split at Hp
    · cases Hp; simp_all [prstateW64]
    cases Hp
  · rintro rfl; cases p <;> decide

theorem prstateOfW64_w64 (p : PRState) : prstateOfW64 (prstateW64 p) = some p :=
  (prstateOfW64_Some _ _).2 rfl

theorem prstateW64_inj (p1 p2 : PRState) (H : prstateW64 p1 = prstateW64 p2) : p1 = p2 := by
  have H' := (prstateOfW64_Some _ _).2 H
  rw [prstateOfW64_w64] at H'
  exact (Option.some.inj H')

theorem prstateW64_ne (p1 p2 : PRState) (Hne : p1 ≠ p2) : prstateW64 p1 ≠ prstateW64 p2 :=
  fun H => Hne (prstateW64_inj _ _ H)

section abs
variable [FfiSyntax]

def inflightsAbs (iv : tracker.Inflights) : Inflights :=
  ⟨sint.Z iv.count', sint.Z iv.size', uint.Z iv.bytes', uint.Z iv.maxBytes'⟩

/-- `none` on a state outside the three: what the pure conjunct of `ownProgress` rules
out. (Until 2026-10-13 also `none` on a learner.) -/
def progressAbs (pv : tracker.Progress) (i : Inflights) : Option Progress :=
  (prstateOfW64 pv.State').map fun st =>
    ⟨pv.Match', pv.Next', pv.sentCommit', st, pv.PendingSnapshot', pv.MsgAppFlowPaused', i,
      pv.IsLearner'⟩

/-- What `progressAbs pv i = some p` says, field by field. -/
theorem progressAbs_Some (pv : tracker.Progress) (i : Inflights) (p : Progress) :
    progressAbs pv i = some p ↔
    pv.IsLearner' = p.learner ∧
    pv.State' = prstateW64 p.state ∧
    pv.Match' = p.matched ∧
    pv.Next' = p.next ∧
    pv.sentCommit' = p.sentCommit ∧
    pv.PendingSnapshot' = p.pendingSnapshot ∧
    pv.MsgAppFlowPaused' = p.paused ∧
    i = p.infl := by
  unfold progressAbs
  obtain ⟨m, n, sc, st, ps, pa, inf, l⟩ := p
  rw [← prstateOfW64_Some]
  cases hs : prstateOfW64 pv.State' with
  | none => simp
  | some st' =>
    simp only [Option.map_some, Option.some.injEq, Progress.mk.injEq]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
      exact ⟨h8, h4 ▸ rfl, h1, h2, h3, h5, h6, h7⟩
    · rintro ⟨h8, h4, h1, h2, h3, h5, h6, h7⟩
      exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

end abs

/-! ### The `Inflights` methods, on the record -/

/-- `Full()` (tracker.v:201):
`in.count == in.size || (in.maxBytes != 0 && in.bytes >= in.maxBytes)`. `Add` panics
when it is `true`. -/
def inflightsFull (i : Inflights) : Bool :=
  decide (i.count = i.size) || (decide (i.maxBytes ≠ 0) && decide (i.maxBytes ≤ i.bytes))

/-- `reset()`: nothing in flight. (`start` is internal.) -/
def inflightsReset (i : Inflights) : Inflights :=
  { i with count := 0, bytes := 0 }

/-- `Add(index, bytes)`, on a window that is not full: one more message, `bytes` more
bytes (`uint64` addition, which wraps). -/
def inflightsAdd (i : Inflights) (b : w64) : Inflights :=
  { i with count := i.count + 1, bytes := (i.bytes + uint.Z b) % 2 ^ 64 }

/-- `FreeLE(to)`'s result is not a function of the record -- it depends on the indices
in the ring buffer -- so it is a relation: the limits are unchanged and no more
messages are in flight than before. -/
def InflightsFreed (i i' : Inflights) : Prop :=
  i'.size = i.size ∧ i'.maxBytes = i.maxBytes ∧ i'.count ≤ i.count

/-- `NewInflights(size, maxBytes)`. -/
def inflightsNew (size maxBytes : w64) : Inflights :=
  ⟨0, sint.Z size, 0, uint.Z maxBytes⟩

/-! ### The `Progress` methods, on the record (progress.go)

Each is the method's effect, read off its body; the spec files give the line. `Match`
is written only by `MaybeUpdate` (Match discipline, notes/raft-replication-model.md).
The first four were in the spec files, on `tracker.Progress`, until 2026-10-02. -/

/-- `ResetState(state)`. -/
def progressResetState (p : Progress) (st : PRState) : Progress :=
  { p with paused := false, pendingSnapshot := W64 0, state := st,
           infl := inflightsReset p.infl }

/-- `BecomeProbe()`: the new `Next`, then the whole update. -/
def progressBecomeProbeNext (p : Progress) : w64 :=
  if p.state = .snapshot then w64Max (p.matched + W64 1) (p.pendingSnapshot + W64 1)
  else p.matched + W64 1

def progressBecomeProbe (p : Progress) : Progress :=
  { progressResetState p .probe with
      next := progressBecomeProbeNext p,
      sentCommit := w64Min p.sentCommit (progressBecomeProbeNext p - W64 1) }

/-- `BecomeReplicate()`. -/
def progressBecomeReplicate (p : Progress) : Progress :=
  { progressResetState p .replicate with next := p.matched + W64 1 }

/-- `BecomeSnapshot(snapshoti)`. -/
def progressBecomeSnapshot (p : Progress) (snapshoti : w64) : Progress :=
  { progressResetState p .snapshot with
      pendingSnapshot := snapshoti, next := snapshoti + W64 1, sentCommit := snapshoti }

/-- `IsPaused()`. -/
def progressIsPaused (p : Progress) : Bool :=
  match p.state with
  | .snapshot => true
  | _ => p.paused

/-- `SentEntries(entries, bytes)`. `StateSnapshot` panics; the spec's premise excludes
it, and this leaves the record alone there. -/
def progressSentEntries (p : Progress) (entries bytes : w64) : Progress :=
  match p.state with
  | .replicate =>
      if 0 < sint.Z entries then
        { p with next := p.next + entries, infl := inflightsAdd p.infl bytes,
                 paused := inflightsFull (inflightsAdd p.infl bytes) }
      else { p with paused := inflightsFull p.infl }
  | .probe => if 0 < sint.Z entries then { p with paused := true } else p
  | .snapshot => p

/-- `SentCommit(commit)`. -/
def progressSentCommit (p : Progress) (commit : w64) : Progress :=
  { p with sentCommit := commit }

/-- `CanBumpCommit(index)`. -/
def progressCanBumpCommit (p : Progress) (index : w64) : Bool :=
  decide (uint.Z p.sentCommit < uint.Z index ∧
          uint.Z p.sentCommit < uint.Z (p.next - W64 1))

/-- `MaybeUpdate(n)`: the new value; it is `p` itself when the ack is stale. The method
returns `decide (matched < n)`. -/
def progressMaybeUpdate (p : Progress) (n : w64) : Progress :=
  if uint.Z p.matched < uint.Z n then
    { p with matched := n, next := w64Max p.next (n + W64 1), paused := false }
  else p

/-- `MaybeDecrTo(rejected, matchHint)`: the answer and the new value. -/
def progressMaybeDecrTo (p : Progress) (rejected matchHint : w64) : Bool × Progress :=
  if p.state = .replicate then
    if uint.Z rejected ≤ uint.Z p.matched then (false, p)
    else
      let nx := p.matched + W64 1
      (true, { p with next := nx, sentCommit := w64Min p.sentCommit (nx - W64 1) })
  else if p.next - W64 1 = rejected then
    let nx := w64Max (w64Min rejected (matchHint + W64 1)) (p.matched + W64 1)
    (true, { p with next := nx, sentCommit := w64Min p.sentCommit (nx - W64 1),
                    paused := false })
  else (false, p)

/-! The `Progress` methods keep `IsLearner` (2026-10-13): what a give-back to the tracker
needs (`ownTracker_lookup`). -/

@[simp] theorem progressSentEntries_learner (p : Progress) (e b : w64) :
    (progressSentEntries p e b).learner = p.learner := by
  unfold progressSentEntries; split <;> (try split) <;> rfl

@[simp] theorem progressMaybeUpdate_learner (p : Progress) (n : w64) :
    (progressMaybeUpdate p n).learner = p.learner := by
  unfold progressMaybeUpdate; split <;> rfl

@[simp] theorem progressMaybeDecrTo_learner (p : Progress) (a b : w64) :
    (progressMaybeDecrTo p a b).2.learner = p.learner := by
  unfold progressMaybeDecrTo; split <;> (try split) <;> rfl

section logstate
variable [FfiSyntax]

/-! ## Physical transitions of the log

`logLast ls` is `lastIndex()` of a log at `ls`, as a `w64`; the `raftLog` specs return
it as an `Int` equation, and `ownRaftLog`'s `Hnowrap` says the `W64` does not wrap. -/

def logLast (ls : LogState) : w64 :=
  W64 (uint.Z ls.prev.index' + ls.sents.length + ls.uents.length)

/-- `ownRaftLog`'s `Hnowrap` (2026-10-16, stage R8a): `lastIndex() + 1` does not wrap. What the
progress lemmas below take; `ownRaftPhysC_prvals_ok` reads it out of the struct. -/
def LogNoWrap (ls : LogState) : Prop :=
  uint.Z ls.prev.index' + (ls.sents.length : Int) + (ls.uents.length : Int) + 1 < 2^64

/-- `logLast` as an integer, once it does not wrap. -/
theorem LogNoWrap.logLast_Z {ls : LogState} (H : LogNoWrap ls) :
    uint.Z (logLast ls) = uint.Z ls.prev.index' + (ls.sents.length : Int) + (ls.uents.length : Int) := by
  unfold LogNoWrap at H; unfold logLast; word

theorem LogNoWrap.logLast {ls : LogState} (H : LogNoWrap ls) : uint.Z (logLast ls) + 1 < 2^64 := by
  rw [H.logLast_Z]; exact H

/-- `lastIndex()`'s result (an `Int` equation, as the `raftLog` specs state it) is `logLast`. -/
theorem logLast_eq_of_Z (ls : LogState) (i : w64)
    (H : uint.Z i = uint.Z ls.prev.index' + (ls.sents.length : Int) + (ls.uents.length : Int)) :
    i = logLast ls := by
  unfold logLast; apply uint_Z_inj.1; rw [← H]; word

/-- `logLast` of a log with the same index range (the same base and lengths): what a log
accessor's give-back asks of a leader (`ownRaftPhys_log_at`) when the last index is unchanged. -/
theorem logLast_le_of_fields {ls ls' : LogState} (hp : ls'.prev.index' = ls.prev.index')
    (hs : ls'.sents.length = ls.sents.length) (hu : ls'.uents.length = ls.uents.length) :
    uint.Z (logLast ls) ≤ uint.Z (logLast ls') := by
  unfold logLast; rw [hp, hs, hu]; exact Int.le_refl _

/-! ### The leader's progress bound (2026-10-16, stage R8a, D11) -/

/-- A leader's view of a peer (`Progress`) against its log (2026-10-16, stage R8a, D11): `Next` at
least `1` and at most one past the last index, `Match` and a pending snapshot's index at most the
last index. -/
def PrOk (ls : LogState) (p : Progress) : Prop :=
  1 ≤ uint.Z p.next ∧ uint.Z p.next ≤ uint.Z (logLast ls) + 1 ∧
  uint.Z p.matched ≤ uint.Z (logLast ls) ∧ uint.Z p.pendingSnapshot ≤ uint.Z (logLast ls)

/-- (2026-10-19, D21 M3) What a leader in the no-snapshot mode (`NGhost.ns`) keeps of a peer
beyond `PrOk`: `Next ≥ 2`, a replicating peer's `Match ≥ 1` (so `BecomeProbe` from
`StateReplicate` keeps `Next ≥ 2`), and no peer waiting for a snapshot. -/
def PrLo (p : Progress) : Prop :=
  2 ≤ uint.Z p.next ∧ (p.state = .replicate → 1 ≤ uint.Z p.matched) ∧ p.state ≠ .snapshot

/-- `PrOk`, and in the no-snapshot mode `PrLo` (2026-10-19, D21 M3): what `PrvalsOk` asks of each
tracked peer of a leader. -/
def PrOkN (ns : Bool) (ls : LogState) (p : Progress) : Prop :=
  PrOk ls p ∧ (ns = true → PrLo p)

/-- `PrOk` is monotone in the log's last index: a leader's log only grows. -/
theorem PrOk.mono {ls ls' : LogState} {p : Progress} (H : PrOk ls p)
    (Hle : uint.Z (logLast ls) ≤ uint.Z (logLast ls')) : PrOk ls' p := by
  unfold PrOk at *; omega

/-- `PrOk` of a value with the same `Next` and `Match` and no larger pending snapshot. -/
theorem PrOk.fields {ls : LogState} {p p' : Progress} (H : PrOk ls p)
    (hn : p'.next = p.next) (hm : p'.matched = p.matched)
    (hs : uint.Z p'.pendingSnapshot ≤ uint.Z p.pendingSnapshot) : PrOk ls p' := by
  unfold PrOk at *; rw [hn, hm]; omega

/-- `PrOk` of a value with the same `Next` and `Match` and no pending snapshot. -/
theorem PrOk.fields0 {ls : LogState} {p p' : Progress} (H : PrOk ls p)
    (hn : p'.next = p.next) (hm : p'.matched = p.matched)
    (hs : p'.pendingSnapshot = W64 0) : PrOk ls p' := by
  unfold PrOk at *; rw [hn, hm, hs]; have := uint_Z_nonneg p.pendingSnapshot; word

/-- The field writes of `stepLeader` that touch none of the three bounded fields. -/
theorem PrOk.setPaused {ls : LogState} {p : Progress} (H : PrOk ls p) (b : Bool) :
    PrOk ls { p with paused := b } :=
  H.fields rfl rfl (Int.le_refl _)

theorem PrOk.setInfl {ls : LogState} {p : Progress} (H : PrOk ls p) (i : Inflights) :
    PrOk ls { p with infl := i } :=
  H.fields rfl rfl (Int.le_refl _)

/-- `pr.PendingSnapshot = 0` (`MsgSnapStatus` rejected). -/
theorem PrOk.clearSnap {ls : LogState} {p : Progress} (H : PrOk ls p) :
    PrOk ls { p with pendingSnapshot := W64 0 } :=
  H.fields0 rfl rfl rfl

/-! One lemma per `Progress` method (`tracker/progress.go`), under `PrOk` of the old value and,
where `Match + 1` or `Next + k` must not wrap, `logLast + 1 < 2^64` (`ownRaftLog`'s `Hnowrap`,
`logLast_nowrap`). -/

theorem PrOk.resetState {ls : LogState} {p : Progress} (H : PrOk ls p) (st : PRState) :
    PrOk ls (progressResetState p st) :=
  H.fields0 rfl rfl rfl

theorem PrOk.becomeProbe {ls : LogState} {p : Progress} (Hnw : LogNoWrap ls)
    (H : PrOk ls p) : PrOk ls (progressBecomeProbe p) := by
  have Hnw := Hnw.logLast
  obtain ⟨h1, h2, h3, h4⟩ := H
  unfold PrOk
  simp only [progressBecomeProbe, progressResetState, progressBecomeProbeNext, w64Max]
  split <;> (try split) <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> word

theorem PrOk.becomeReplicate {ls : LogState} {p : Progress} (Hnw : LogNoWrap ls)
    (H : PrOk ls p) : PrOk ls (progressBecomeReplicate p) := by
  have Hnw := Hnw.logLast
  obtain ⟨h1, h2, h3, h4⟩ := H
  unfold PrOk
  simp only [progressBecomeReplicate, progressResetState]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> word

theorem PrOk.becomeSnapshot {ls : LogState} {p : Progress} {i : w64}
    (Hnw : LogNoWrap ls) (H : PrOk ls p) (Hi : uint.Z i ≤ uint.Z (logLast ls)) :
    PrOk ls (progressBecomeSnapshot p i) := by
  have Hnw := Hnw.logLast
  obtain ⟨h1, h2, h3, h4⟩ := H
  unfold PrOk
  simp only [progressBecomeSnapshot, progressResetState]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> word

/-- `SentEntries(entries, bytes)` of entries from `Next` on, within the log. -/
theorem PrOk.sentEntries {ls : LogState} {p : Progress} {entries bytes : w64}
    (Hnw : LogNoWrap ls) (H : PrOk ls p) (He : 0 ≤ sint.Z entries)
    (Hb : uint.Z p.next + sint.Z entries ≤ uint.Z (logLast ls) + 1) :
    PrOk ls (progressSentEntries p entries bytes) := by
  have Hnw := Hnw.logLast
  obtain ⟨h1, h2, h3, h4⟩ := H
  have He' : uint.Z entries = sint.Z entries := by word
  unfold PrOk progressSentEntries
  split <;> (try split) <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> word

theorem PrOk.sentCommit {ls : LogState} {p : Progress} (H : PrOk ls p) (c : w64) :
    PrOk ls (progressSentCommit p c) :=
  H.fields rfl rfl (Int.le_refl _)

/-- `MaybeUpdate(n)` of an index within the log. -/
theorem PrOk.maybeUpdate {ls : LogState} {p : Progress} {n : w64}
    (H : PrOk ls p) (Hn : uint.Z n ≤ uint.Z (logLast ls)) :
    PrOk ls (progressMaybeUpdate p n) := by
  obtain ⟨h1, h2, h3, h4⟩ := H
  unfold PrOk progressMaybeUpdate
  simp only [w64Max]
  split <;> (try split) <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> word

/-- `MaybeDecrTo(rejected, matchHint)`: both arms (in the probe arm `rejected = Next - 1`, within
the log by `PrOk` itself). -/
theorem PrOk.maybeDecrTo {ls : LogState} {p : Progress} {rejected matchHint : w64}
    (Hnw : LogNoWrap ls) (H : PrOk ls p) :
    PrOk ls (progressMaybeDecrTo p rejected matchHint).2 := by
  have Hnw := Hnw.logLast
  obtain ⟨h1, h2, h3, h4⟩ := H
  unfold PrOk progressMaybeDecrTo
  simp only [w64Max, w64Min]
  split
  · split <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> word
  · split
    · rename_i Hr
      have Hr' : uint.Z rejected = uint.Z p.next - 1 := by
        rw [← Hr]; word
      split <;> split <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> word
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> word

/-! `PrOkN`, one lemma per `Progress` method (2026-10-19, D21 M3): `PrOk`'s, and `PrLo`'s under the
premise the method needs in the no-snapshot mode. -/

theorem PrOkN.prOk {ns : Bool} {ls : LogState} {p : Progress} (H : PrOkN ns ls p) : PrOk ls p :=
  H.1

theorem PrOkN.of_off {ls : LogState} {p : Progress} (H : PrOk ls p) : PrOkN false ls p :=
  ⟨H, fun h => by cases h⟩

theorem PrOkN.mono {ns : Bool} {ls ls' : LogState} {p : Progress} (H : PrOkN ns ls p)
    (Hle : uint.Z (logLast ls) ≤ uint.Z (logLast ls')) : PrOkN ns ls' p :=
  ⟨H.1.mono Hle, H.2⟩

/-- The same `Next`, `Match` and state, no larger pending snapshot. -/
theorem PrOkN.fields {ns : Bool} {ls : LogState} {p p' : Progress} (H : PrOkN ns ls p)
    (hn : p'.next = p.next) (hm : p'.matched = p.matched) (hst : p'.state = p.state)
    (hs : uint.Z p'.pendingSnapshot ≤ uint.Z p.pendingSnapshot) : PrOkN ns ls p' :=
  ⟨H.1.fields hn hm hs, fun h => by
    obtain ⟨h1, h2, h3⟩ := H.2 h
    exact ⟨by rw [hn]; exact h1, (fun h' => by rw [hm]; exact h2 (hst ▸ h')), by rw [hst]; exact h3⟩⟩

theorem PrOkN.setPaused {ns : Bool} {ls : LogState} {p : Progress} (H : PrOkN ns ls p) (b : Bool) :
    PrOkN ns ls { p with paused := b } :=
  H.fields rfl rfl rfl (Int.le_refl _)

theorem PrOkN.setInfl {ns : Bool} {ls : LogState} {p : Progress} (H : PrOkN ns ls p)
    (i : Inflights) : PrOkN ns ls { p with infl := i } :=
  H.fields rfl rfl rfl (Int.le_refl _)

theorem PrOkN.clearSnap {ns : Bool} {ls : LogState} {p : Progress} (H : PrOkN ns ls p) :
    PrOkN ns ls { p with pendingSnapshot := W64 0 } :=
  ⟨H.1.clearSnap, fun h => by
    obtain ⟨h1, h2, h3⟩ := H.2 h
    exact ⟨h1, h2, h3⟩⟩

theorem PrOkN.sentCommit {ns : Bool} {ls : LogState} {p : Progress} (H : PrOkN ns ls p) (c : w64) :
    PrOkN ns ls (progressSentCommit p c) :=
  H.fields rfl rfl rfl (Int.le_refl _)

/-- `BecomeProbe()`: in the no-snapshot mode, from `StateReplicate` (`MsgUnreachable`, a
rejection while replicating), where `Match ≥ 1`. -/
theorem PrOkN.becomeProbe {ns : Bool} {ls : LogState} {p : Progress} (Hnw : LogNoWrap ls)
    (H : PrOkN ns ls p) (Hrep : ns = true → p.state = .replicate) :
    PrOkN ns ls (progressBecomeProbe p) := by
  refine ⟨H.1.becomeProbe Hnw, fun h => ?_⟩
  have Hnw' := Hnw.logLast
  obtain ⟨-, -, h3, -⟩ := H.1
  obtain ⟨-, h2, -⟩ := H.2 h
  have hr := Hrep h
  have hm := h2 hr
  unfold PrLo
  simp only [progressBecomeProbe, progressResetState, progressBecomeProbeNext, hr]
  refine ⟨?_, (fun h => by cases h), (fun h => by cases h)⟩
  simp only [reduceCtorEq, ↓reduceIte]
  word

/-- `BecomeReplicate()`: in the no-snapshot mode, of a peer with `Match ≥ 1`. -/
theorem PrOkN.becomeReplicate {ns : Bool} {ls : LogState} {p : Progress} (Hnw : LogNoWrap ls)
    (H : PrOkN ns ls p) (Hm : ns = true → 1 ≤ uint.Z p.matched) :
    PrOkN ns ls (progressBecomeReplicate p) := by
  refine ⟨H.1.becomeReplicate Hnw, fun h => ?_⟩
  have Hnw' := Hnw.logLast
  obtain ⟨-, -, h3, -⟩ := H.1
  have hm := Hm h
  unfold PrLo
  simp only [progressBecomeReplicate, progressResetState]
  refine ⟨by word, (fun _ => hm), (fun h => by cases h)⟩

/-- `BecomeSnapshot(i)`: only outside the no-snapshot mode. -/
theorem PrOkN.becomeSnapshot {ls : LogState} {p : Progress} {i : w64}
    (Hnw : LogNoWrap ls) (H : PrOkN false ls p) (Hi : uint.Z i ≤ uint.Z (logLast ls)) :
    PrOkN false ls (progressBecomeSnapshot p i) :=
  PrOkN.of_off (H.1.becomeSnapshot Hnw Hi)

/-- `SentEntries(entries, bytes)` of entries from `Next` on, within the log. -/
theorem PrOkN.sentEntries {ns : Bool} {ls : LogState} {p : Progress} {entries bytes : w64}
    (Hnw : LogNoWrap ls) (H : PrOkN ns ls p) (He : 0 ≤ sint.Z entries)
    (Hb : uint.Z p.next + sint.Z entries ≤ uint.Z (logLast ls) + 1) :
    PrOkN ns ls (progressSentEntries p entries bytes) := by
  refine ⟨H.1.sentEntries Hnw He Hb, fun h => ?_⟩
  have Hnw' := Hnw.logLast
  obtain ⟨h1, h2, h3⟩ := H.2 h
  have He' : uint.Z entries = sint.Z entries := by word
  unfold PrLo progressSentEntries
  split <;> (try split) <;> (try exact ⟨h1, h2, h3⟩)
  all_goals rename_i hst
  all_goals simp only [hst] at h2 h3 ⊢
  all_goals first
    | exact absurd rfl h3
    | exact ⟨by word, h2, h3⟩

/-- `MaybeUpdate(n)` of an index within the log. -/
theorem PrOkN.maybeUpdate {ns : Bool} {ls : LogState} {p : Progress} {n : w64}
    (Hnw : LogNoWrap ls) (H : PrOkN ns ls p) (Hn : uint.Z n ≤ uint.Z (logLast ls)) :
    PrOkN ns ls (progressMaybeUpdate p n) := by
  refine ⟨H.1.maybeUpdate Hn, fun h => ?_⟩
  have Hnw' := Hnw.logLast
  obtain ⟨h1, h2, h3⟩ := H.2 h
  unfold PrLo progressMaybeUpdate
  simp only [w64Max]
  split
  · refine ⟨?_, fun h' => ?_, h3⟩
    · split <;> word
    · rename_i hlt; have := uint_Z_nonneg p.matched; word
  · exact ⟨h1, h2, h3⟩

/-- `MaybeDecrTo(rejected, matchHint)`: in the no-snapshot mode, a rejection past index `1` with a
hint of at least `1` and at most the rejected index (`isMessage`'s clause of a rejecting
`MsgAppResp`, and the leader's `findConflictByTerm` above index `0`). -/
theorem PrOkN.maybeDecrTo {ns : Bool} {ls : LogState} {p : Progress} {rejected matchHint : w64}
    (Hnw : LogNoWrap ls) (H : PrOkN ns ls p)
    (Hr : ns = true → 2 ≤ uint.Z rejected ∧ 1 ≤ uint.Z matchHint ∧
      uint.Z matchHint ≤ uint.Z rejected) :
    PrOkN ns ls (progressMaybeDecrTo p rejected matchHint).2 := by
  refine ⟨H.1.maybeDecrTo Hnw, fun h => ?_⟩
  have Hnw' := Hnw.logLast
  obtain ⟨o1, o2, o3, o4⟩ := H.1
  obtain ⟨h1, h2, h3⟩ := H.2 h
  obtain ⟨r1, r2, r3⟩ := Hr h
  unfold PrLo progressMaybeDecrTo
  simp only [w64Max, w64Min]
  split
  · rename_i hrep
    have hm := h2 hrep
    split
    · exact ⟨h1, h2, h3⟩
    · refine ⟨by word, (fun _ => hm), by rw [hrep]; exact fun h => by cases h⟩
  · split
    · rename_i hrep hr
      have Hr' : uint.Z rejected = uint.Z p.next - 1 := by rw [← hr]; word
      refine ⟨?_, h2, h3⟩
      split <;> split <;> word
    · exact ⟨h1, h2, h3⟩

/-- `unstable.offset`, which `ownRaftLog` pins to the end of the stable part
(`Hoffset`). -/
def logOffset (ls : LogState) : Int :=
  uint.Z ls.prev.index' + (ls.sents.length : Int) + 1

/-- `nextUnstableEnts()`: the unstable entries not yet handed out by a `Ready`
(`u.entries[offsetInProgress-offset:]`). -/
def nextUnstable (ls : LogState) : List EntryM :=
  ls.uents.drop (uint.Z ls.inprogress - logOffset ls).toNat
-- (Both moved here from `InvReadylog.lean` on 2026-10-10: `ownRaftPhys` states
-- `NGhost.unst` on `nextUnstable`.)

/-- `raftLog.append` at the end of the log: the batch joins the unstable suffix
(`Spec/raftLog__append.lean`). -/
def logAppend (ls : LogState) (ents : List EntryM) : LogState :=
  { ls with uents := ls.uents ++ ents }

/-- A snapshot's id, `(Metadata.Term, Metadata.Index)` -- what `raft.restore` builds as
`id := entryID{term, index}`. -/
def snapId (sv : SnapshotM) : entryID :=
  entryID.mk sv.Metadata'.Term' sv.Metadata'.Index'

/-- `raftLog.restore(s)` (`Spec/raftLog__restore.lean`): the log is the snapshot -- its
id is the boundary, nothing after it, committed up to it, `applied` untouched, the
snapshot pending. `unstable.restore` sets `offsetInProgress` to the new offset;
`applying` and the unpersisted entries are untouched. (2026-10-15, stage S) The snapshot `k`
(its id, lists and `AutoLeave`) joins the ones the node may send (`ksn`). -/
def logRestore (ls : LogState) (k : SnapTrip) : LogState :=
  ⟨k.sid, [], [], k.sid.index', ls.applied, some k.sid, k.sid.index' + W64 1, ls.applying,
   ls.unpersisted, ls.stored, ls.apsize, ls.apmax, ls.storage, ls.ksn ++ [k], ls.fl, false⟩

/-- A snapshot as the protocol knows it (2026-10-15, stage S): its id, the lists behind its
`ConfState` and its `AutoLeave`. -/
def snapTrip (sv : SnapshotM) (cl : CSLists) : SnapTrip :=
  ⟨snapId sv, cl, sv.Metadata'.ConfState'.AutoLeave'⟩

/-- (D22 S-b′3) A `MsgSnap`'s abstraction carries its snapshot's trip. -/
theorem msgSnapTrip_absSnapFrom (m : MessageM) (src term : w64) (sv : SnapshotM) (cl : CSLists) :
    msgSnapTrip (absSnapFrom m src term sv cl) = snapTrip sv cl := rfl

/-! `stamp`, `appendEntry`'s stamping loop, is in `Protocol/Model.lean` (since
2026-10-01: the model's `Step.win` and `Step.propose` stamp too). -/

end logstate

/-! ## The physical abstract state

`NState` is what `ownRaftPhys r id s` (`InvRaftPhys.lean`) is indexed by: the **most
abstract description of the raft struct and the heap hanging off it that still lets
every Go-level spec be stated on `ownRaftPhys` alone**. It is the first of three layers
(notes/decisions.md, "Three layers"):

    Go code and heap  --ownRaftPhys-->  NState
    NState            --NStateRel---->  PState  (Protocol/Model.lean)
    PState            --ownRaftGhost->  protocol properties

**The rule.** If a function cannot be specified with `ownRaftPhys`, refine `NState`
(and `ownRaftPhys` with it) until it can. Do *not* introduce a variant predicate -- a
second ownership predicate for the struct, or one with an extra parameter -- for one
caller's benefit. Until 2026-09-22 there were three (`own_raft_phys_at` with a free
`r.step`, `own_raft_bare` and `own_raft_notrk` with the tracker and/or the log cut
out), and every spec stated on one of them was a spec its callers had to convert into
and out of. The three fields below that are not protocol state replace them:

* `stepfn` is `r.step`. `becomeFollower` writes it *before* calling `reset`, and
  `newRaft` calls `becomeFollower` while it is still nil, so it cannot be a function
  of `role`.
* `progress` is the progress map, id to `*Progress`. Nothing on the election path
  inserts into or deletes from it, so it is stable across every call, and a proof that
  borrows one peer's `Progress` can hand it back before a call and borrow it again
  after, at the same key.
* `prvals` is each peer's `Progress`, as the record `Progress` (with its `Inflights`
  window): what `*pr` and `*pr.Inflights` hold for the `pr` that `progress` maps the
  peer to. (Until 2026-10-02 a pair of Goose values, `tracker.Progress ×
  tracker.Inflights`.) `ownTracker` is indexed by it (`InvTracker.lean`), so a spec
  says how it changes the `Progress`es, or quantifies the new values.
  `maybeSendAppend` needs it: it reads `pr` before `r.send` and calls `pr.SentEntries`
  after, which panics in `StateSnapshot` and, through `Inflights.Add`, on a full window
  -- so it must know, after a call made with the struct sealed, that `pr` still holds
  what it read. (Until 2026-09-29 that was done by a field `lent : option
  ProgressTracker.t`: the tracker's heap was *lent* out of `ownRaftPhys` to the caller,
  and every function that touched the tracker took `lent = None`; before 2026-09-21,
  the variant predicate `own_raft_bare`. A proposed replacement, a "pin" recording one
  `Progress` value, was rejected: `NState` holds only physical state.)
* `log` is `r.raftLog`, the log's location (it never changes).
* `logst` is the log's state (`LogState`).
* `prevote` is `r.preVote` (since 2026-10-04; until then a scope conjunct of
  `ownRaftPhys` pinned it to `false`). Written only by `newRaft`, from
  `Config.PreVote`.

`role` is the *physical* role, `r.state` (`PRole`, four values); `toPState` reads a
pre-candidate as a follower.

The first six fields have `PState`'s names, so that a spec's `s.term` reads the same
as it always did; `role` is the physical role. -/

/-- Ghost facts the raft struct keeps for `node.go` (2026-10-10), lower bounds that only a
`Ready` resets: `outlb` is at most the number of queued messages (`r.msgs` and
`r.msgsAfterAppend`; they only grow until `acceptReady` empties them), and `unst` says
that some unstable entry has not been handed out (`nextUnstable` is non-empty, or a
snapshot is pending). `node.go`'s `run` abandons a computed `Ready` and may later send
it after all, when `HasReady` reports nothing new: that is right only because whatever
the abandoned `Ready` held is still there (`ownRawNodeReady_abandon`, `RNState.outlb`).
`ownRaftPhys` states both (`Hgh_out`, `Hgh_unst`); every step but a storage
acknowledgement keeps them (`NetFrame`, `LocalFrame`). -/
structure NGhost where
  outlb : Nat := 0
  unst : Bool := false
  /-- (2026-10-17, pre-vote at the `RawNode` layer) a term ceiling: every queued message is of a
  term at most the node's or this (`OutTermOk`). Only the `RawNode` raises it, before a step, to a
  term the budget covers (a received message's, or one past the node's before a `MsgHup`): a
  `MsgPreVote` is at the next term and a granted `MsgPreVoteResp` at the requester's. -/
  tc : w64 := W64 0
  /-- (2026-10-19, D21 M3) **The no-snapshot mode**: a node of a static cluster with a non-empty
  bootstrap log whose storage is never compacted past index `1` (`storCap`, `ownRaftPhys`'s
  `Hns`). A leader then keeps every peer's `Next ≥ 2` (`PrLo`), so `term(Next - 1)` and
  `entries(Next)` never fail and it sends no `MsgSnap` (D21 M0's (N)). Set once, when the node
  is built (`ownRaftPhys_set_ns`), never changed: every step and `Ready` keeps it. -/
  ns : Bool := false
  /-- (2026-10-19, D21 M2r) **Leader transfer off**: the node never records a transferee
  (`leadTransferee = 0`, `ownRaftPhys`'s `Hxf`) and queues no message of a type the model does not
  describe (`MsgTimeoutNow`, a forwarded `MsgTransferLeader`): `raft.Step` takes no
  `MsgTransferLeader` (`RestMsgOk`). On when the struct is built (`newRaft`, its queues empty:
  the default), turned off by a ghost step (`ownRaftPhysC_xf_off`) when the node's construction
  leaves the cluster's no-transfer mode (`RestartNode`, `Bootstrap` outside it), so that a node
  is in it exactly when in the cluster's mode (`NsLink`; 2026-10-19, D22 S-a:
  `RaftNames.reNoXfer`, independent of the no-snapshot mode, which until then implied it). With
  the no-snapshot mode it makes the queued messages `SentMsgOk` (`XfOk`). (D22 S-c) With the
  boot flag `bt` instead: the no-snapshot mode no longer enters. -/
  xf : Bool := true
  /-- (2026-10-20, D22 S-c) **Past term `0` for good**: the node's term is not `0` (`ownRaftPhys`'s
  `Hxf`, `XfOk`), which `SentMsgOk`'s stamped terms need. Off when the struct is built (`newRaft`,
  at term `0`), set with leader transfer's flag when the node's construction is of a cluster with
  a bootstrap log (`Bootstrap`, at term `1`; `ownRaftPhys_set_ns`), at the cluster's no-transfer
  mode (`NsLink`: `RaftNames.reNoXfer`, which needs a bootstrap log, `reNoXfer_ok`). Until D22
  S-c the no-snapshot mode (`ns`) gave the term, so that `SentMsgOk` was of both modes. -/
  bt : Bool := false
deriving DecidableEq



structure NState [FfiSyntax] where
  term : w64
  vote : w64
  lead : w64
  /-- `r.state`; see `PRole` -/
  role : PRole
  votes : GMap w64 Bool
  outbox : List Msg
  /-- `r.step` -/
  stepfn : GoFunc
  /-- Whether `r.tick` has been set (2026-10-09): every `becomeX` sets it to
  `r.tickElection` or `r.tickHeartbeat` (`ownRaftPhys`'s `Htick`); only `newRaft`'s
  struct, before its `becomeFollower`, has it `nil`. `NStateWf` says it is set. -/
  ticking : Bool
  /-- `r.trk.Progress`, as a map -/
  progress : GMap w64 Loc
  /-- `r.raftLog` -/
  log : Loc
  /-- the log's abstract state -/
  logst : LogState
  /-- `*pr` with its window, per peer -/
  prvals : GMap w64 Progress
  /-- `r.preVote` (2026-10-04) -/
  prevote : Bool
  /-- ghost lower bounds for `node.go` (2026-10-10), see `NGhost` -/
  gh : NGhost := {}
  /-- the read-index state (2026-10-12), see `RdState` -/
  rd : RdState := {}
  /-- `r.leadTransferee` (2026-10-13): the leader-transfer target, `0` for none. Only a
  leader's `MsgTransferLeader` sets it (to another node: `ownRaftPhys` keeps it `≠ id`);
  `reset` (every `becomeX` but `becomePreCandidate`) and `abortLeaderTransfer` clear it.
  Invisible to the protocol (`toPState`). -/
  lt : w64 := W64 0
  /-- `r.pendingConfIndex` (2026-10-13, reconfiguration stage D): the index of the last
  conf-change entry the leader appended (or, after `becomeLeader`, its last index, which may
  hide one), against which `stepLeader` refuses another conf change until it is applied.
  `reset` clears it, `becomeLeader` sets it, `stepLeader`'s proposal loop moves it.
  Invisible to the protocol (`toPState`). -/
  pci : w64 := W64 0
  /-- `r.isLearner` (2026-10-13, reconfiguration stage L; until then a scope conjunct pinned
  it to `false`): what `switchToConfig` last stored, `ok && pr.IsLearner` for the node's own
  `Progress`. Read only by `switchToConfig` itself, right after the store. Invisible to the
  protocol (`toPState`). -/
  isLearner : Bool := false
  /-- `r.stepDownOnRemoval` (2026-10-13, reconfiguration stage A2), recorded: a removed or
  demoted leader steps down in `switchToConfig` exactly when it is set. Never written after
  `newRaft` (`Config.StepDownOnRemoval`). Invisible to the protocol (`toPState`). -/
  sdr : Bool := false
  /-- `r.checkQuorum` (2026-10-17; until then a scope conjunct of `ownRaftPhys` pinned it to
  `false`), recorded: a leader past its election timeout steps `MsgCheckQuorum` and steps down
  when the voters it heard from are no quorum; a node that heard from a leader within the
  election timeout ignores a vote request of a higher term (`Step`'s lease check); a node
  answers a stale leader's `MsgApp`/`MsgHeartbeat` with an empty `MsgAppResp`. Never written
  after `newRaft` (`Config.CheckQuorum`). Invisible to the protocol (`toPState`). -/
  cq : Bool := false

/-- What `switchToConfig` stores in `r.isLearner` (2026-10-13): `ok && pr.IsLearner` for the
node's own `Progress` in the new progress map `prs` -- tracked, and outside the voters `cfg`
(`LearnerFlags`). -/
def learnerOf (cfg : GSet w64) (prs : GMap w64 Loc) (id : w64) : Bool :=
  decide (id ∈ domSet prs ∧ id ∉ cfg)

/-! ### The leader's progress bound on a state (2026-10-16, stage R8a, D11) -/

section prvals_ok
variable [FfiSyntax]

/-- Every tracked peer of a leader is within its log (vacuous for a non-leader: a follower's log
may shrink, and `reset` re-initializes the progress on winning). A pure conjunct of `ownRaftPhys`
(`InvRaftPhys.lean`). -/
def PrvalsOk (s : NState) : Prop :=
  s.role = .leader → ∀ v p, s.prvals !! v = some p → PrOkN s.gh.ns s.logst p

/-- `PrvalsOk` depends on `role`, `prvals`, `logst` and the mode only. -/
theorem PrvalsOk.of_fields {s s' : NState} (H : PrvalsOk s) (hr : s'.role = s.role)
    (hp : s'.prvals = s.prvals) (hl : s'.logst = s.logst) (hg : s'.gh.ns = s.gh.ns := by rfl) :
    PrvalsOk s' := by
  unfold PrvalsOk at *; rw [hr, hp, hl, hg]; exact H

theorem PrvalsOk.not_leader {s : NState} (h : s.role ≠ .leader) : PrvalsOk s :=
  fun hl => absurd hl h

/-- One peer's `Progress` written. -/
theorem PrvalsOk.insert {s : NState} {pvs : GMap w64 Progress}
    (H : PrvalsOk { s with prvals := pvs }) {k : w64} {p' : Progress}
    (Hp : s.role = .leader → PrOkN s.gh.ns s.logst p') :
    PrvalsOk { s with prvals := <[k := p']> pvs } := by
  intro Hl v p Hv
  simp only at Hl Hv ⊢
  by_cases hk : k = v
  · subst hk; rw [GMap.lookup_insert_eq] at Hv; cases Hv; exact Hp Hl
  · rw [GMap.lookup_insert_ne _ _ hk] at Hv; exact H Hl v p Hv

/-- The log changed, its last index not lower at a leader. -/
theorem PrvalsOk.mono_log {s : NState} {ls' : LogState} (H : PrvalsOk s)
    (Hle : s.role = .leader → uint.Z (logLast s.logst) ≤ uint.Z (logLast ls')) :
    PrvalsOk { s with logst := ls' } :=
  fun Hl v p Hv => (H Hl v p Hv).mono (Hle Hl)

/-- The bound of one tracked peer. -/
theorem PrvalsOk.lookup {s : NState} (H : PrvalsOk s) (Hl : s.role = .leader) {v : w64}
    {p : Progress} (Hv : s.prvals !! v = some p) : PrOkN s.gh.ns s.logst p :=
  H Hl v p Hv

/-- (D21 M3) A leader in the no-snapshot mode tracking any peer has a last index of at least `1`:
the peer's `Next` is at least `2` and at most one past it. -/
theorem PrvalsOk.logLast_pos {s : NState} (H : PrvalsOk s) (Hl : s.role = .leader)
    (hns : s.gh.ns = true) {v : w64} {p : Progress} (Hv : s.prvals !! v = some p) :
    1 ≤ uint.Z (logLast s.logst) := by
  obtain ⟨⟨h1, h2, -, -⟩, h⟩ := H Hl v p Hv
  obtain ⟨h3, -, -⟩ := h hns
  omega

/-- What `reset`'s `Visit` closure writes into the peer `v`'s `Progress`, with `li` the log's last
index (`raft.go`'s `reset`: `*pr = Progress{Match: 0, Next: lastIndex+1, ...}; if id == r.id {
pr.Match = lastIndex }`): `Next = lastIndex + 1`, `Match = 0` (`lastIndex` for the node itself),
no pending snapshot, `StateProbe` (the zero `Progress`'s state). -/
def ResetPr (id li v : w64) (p : Progress) : Prop :=
  p.next = li + W64 1 ∧ p.matched = (if v = id then li else W64 0) ∧
  p.pendingSnapshot = W64 0 ∧ p.state = .probe

/-- `PrOk` of a value `reset`'s closure writes: `Next = lastIndex + 1`, `Match` `0` or `lastIndex`,
no pending snapshot. -/
theorem PrOk.of_reset_vals {ls : LogState} {p : Progress} (Hnw : LogNoWrap ls)
    (hn : p.next = logLast ls + W64 1) (hm : p.matched = W64 0 ∨ p.matched = logLast ls)
    (hs : p.pendingSnapshot = W64 0) : PrOk ls p := by
  have Hnw := Hnw.logLast
  unfold PrOk; rw [hn, hs]
  rcases hm with hm | hm <;> rw [hm] <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> word

/-- `PrOkN` of a probing value `reset`'s closure writes: in the no-snapshot mode, at a last index of
at least `1`. -/
theorem PrOkN.of_reset_vals {ns : Bool} {ls : LogState} {p : Progress} (Hnw : LogNoWrap ls)
    (hn : p.next = logLast ls + W64 1) (hm : p.matched = W64 0 ∨ p.matched = logLast ls)
    (hs : p.pendingSnapshot = W64 0) (hst : p.state = .probe)
    (Hli : ns = true → 1 ≤ uint.Z (logLast ls)) : PrOkN ns ls p := by
  refine ⟨PrOk.of_reset_vals Hnw hn hm hs, fun h => ?_⟩
  have Hnw' := Hnw.logLast
  have hl := Hli h
  unfold PrLo
  rw [hn, hst]
  exact ⟨by word, (fun h => by cases h), (fun h => by cases h)⟩

theorem ResetPr.prOk {id v : w64} {ls : LogState} {p : Progress}
    (Hnw : LogNoWrap ls) (H : ResetPr id (logLast ls) v p) : PrOk ls p := by
  obtain ⟨h1, h2, h3, -⟩ := H
  refine PrOk.of_reset_vals Hnw h1 ?_ h3
  rw [h2]; split
  · exact .inr rfl
  · exact .inl rfl

/-- `PrOkN` of a value `reset`'s closure writes: in the no-snapshot mode, at a log whose last
index is at least `1` (a node's log holds the non-empty bootstrap log). -/
theorem ResetPr.prOkN {ns : Bool} {id v : w64} {ls : LogState} {p : Progress}
    (Hnw : LogNoWrap ls) (H : ResetPr id (logLast ls) v p)
    (Hli : ns = true → 1 ≤ uint.Z (logLast ls)) : PrOkN ns ls p := by
  refine ⟨H.prOk Hnw, fun h => ?_⟩
  have Hnw' := Hnw.logLast
  have hl := Hli h
  obtain ⟨h1, -, -, h4⟩ := H
  unfold PrLo
  rw [h1, h4]
  exact ⟨by word, (fun h => by cases h), (fun h => by cases h)⟩

/-- What a `Changer`'s new progress map holds, given the old one (`InvApplyConfC.lean`,
`ownResult_transfer`): each `Progress` is a copy of the old one at that id (`Match`, `Next` and the
pending snapshot kept) or fresh (`initProgress`: `Match = 0`, `Next = max(LastIndex, 1)`, no
pending snapshot), `li` the `Changer`'s `LastIndex`. -/
def PrKeptAt (old : GMap w64 Progress) (li k : w64) (p' : Progress) : Prop :=
  (∃ p, old !! k = some p ∧ p'.matched = p.matched ∧ p'.next = p.next ∧
    p'.pendingSnapshot = p.pendingSnapshot ∧ p'.state = p.state) ∨
  (p'.matched = W64 0 ∧ uint.Z p'.next = max (uint.Z li) 1 ∧ p'.pendingSnapshot = W64 0 ∧
    p'.state = .probe)

def PrKept (old pvs : GMap w64 Progress) (li : w64) : Prop :=
  ∀ k p', pvs !! k = some p' → PrKeptAt old li k p'

/-- `PrKeptAt` says what `MatchKept` says of `Match`. -/
theorem PrKeptAt.matchKept {old : GMap w64 Progress} {li k : w64} {p' : Progress}
    (H : PrKeptAt old li k p') :
    uint.Z p'.matched = 0 ∨ ∃ p, old !! k = some p ∧ p.matched = p'.matched := by
  rcases H with ⟨p, Hp, hm, -, -, -⟩ | ⟨hm, -, -, -⟩
  · exact .inr ⟨p, Hp, hm.symm⟩
  · left; rw [hm]; rfl

/-- `PrKept` at the log's last index keeps `PrOk`. -/
theorem PrKept.prOk {old pvs : GMap w64 Progress} {ls : LogState}
    (H : PrKept old pvs (logLast ls)) (Hold : ∀ v p, old !! v = some p → PrOk ls p)
    (v : w64) (p : Progress) (Hv : pvs !! v = some p) : PrOk ls p := by
  rcases H v p Hv with ⟨p0, Hp0, hm, hn, hs, -⟩ | ⟨hm, hn, hs, -⟩
  · exact (Hold v p0 Hp0).fields hn hm (by rw [hs]; exact Int.le_refl _)
  · unfold PrOk; rw [hm, hn, hs]
    have := uint_Z_nonneg (logLast ls)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> word

/-- `PrKept` keeps `PrOkN` (2026-10-19, D21 M3): a kept peer's is the old one; a fresh one is
probing at `max(lastIndex, 1)`, past `1` in the no-snapshot mode once the last index is (a
leader's log holds the bootstrap log and its own entry). -/
theorem PrKept.prOkN {ns : Bool} {old pvs : GMap w64 Progress} {ls : LogState}
    (H : PrKept old pvs (logLast ls)) (Hold : ∀ v p, old !! v = some p → PrOkN ns ls p)
    (Hli : ns = true → 2 ≤ uint.Z (logLast ls))
    (v : w64) (p : Progress) (Hv : pvs !! v = some p) : PrOkN ns ls p := by
  refine ⟨H.prOk (fun v p h => (Hold v p h).1) v p Hv, fun h => ?_⟩
  rcases H v p Hv with ⟨p0, Hp0, hm, hn, hs, hst⟩ | ⟨hm, hn, hs, hst⟩
  · obtain ⟨h1, h2, h3⟩ := (Hold v p0 Hp0).2 h
    refine ⟨by rw [hn]; exact h1, (fun h' => by rw [hm]; exact h2 (hst ▸ h')), by rw [hst]; exact h3⟩
  · have hl := Hli h
    unfold PrLo; rw [hst]
    refine ⟨by omega, (fun h => by cases h), (fun h => by cases h)⟩

end prvals_ok

section phys_state
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- Which of the three `stepX` functions `r.step` holds in each role. The `becomeX`
functions assign these, and `Step` dispatches a message it does not handle inline
through `r.step(m)`. -/
def stepFuncOf : PRole → GoFunc
  | .follower => functions stepFollower []
  | .candidate | .preCandidate => functions stepCandidate []
  | .leader => functions stepLeader []

/-- The two functions `r.tick` holds once set: the method values `r.tickElection` (a
non-leader's) and `r.tickHeartbeat` (a leader's). Which one is not tied to the role:
both are safe to run in any role (2026-10-09). -/
def TickFnOk (r : Loc) (f : GoFunc) : Prop :=
  f = methods (go.GoType.PointerType raft.ty) go!"tickElection" #r ∨
  f = methods (go.GoType.PointerType raft.ty) go!"tickHeartbeat" #r

/-! ### Transitions of the physical state

Each mirrors a Go function exactly, `r.step` included, and leaves the fields the
function does not write alone. -/

def sendMsgs (s : NState) (ms : List Msg) : NState :=
  { s with outbox := s.outbox ++ ms }

/-- `reset(term)`: clears `Vote` only when the term actually changes, always clears
`lead` and the tally. -/
def resetTo0 (s : NState) (term : w64) : NState :=
  { s with term := term, vote := if term = s.term then s.vote else W64 0, lead := W64 0,
           votes := ∅, lt := W64 0 }

/-- (2026-10-12) and the fresh `readOnly` object `reset` installs last; (2026-10-13) and
`pendingConfIndex` cleared. -/
def resetTo (s : NState) (term : w64) : NState :=
  { resetTo0 s term with rd := { s.rd with ro := ⟨[], ∅, W64 0⟩ }, pci := W64 0 }

def becomeFollower (s : NState) (term lead : w64) : NState :=
  { resetTo s term with lead := lead, role := .follower, stepfn := stepFuncOf .follower,
                        ticking := true }

def becomeCandidate (id : w64) (s : NState) : NState :=
  { resetTo s (s.term + W64 1) with vote := id, role := .candidate,
                                    stepfn := stepFuncOf .candidate, ticking := true }

/-- `becomePreCandidate` (raft.go:912): `r.step`, the tally (`ResetVotes`), `lead :=
None` and the state. **Term and vote unchanged**, and no `reset`: the `Progress` values
are left alone. -/
def becomePrecandidate (s : NState) : NState :=
  { s with role := .preCandidate, lead := W64 0, votes := ∅,
           stepfn := stepFuncOf .preCandidate, ticking := true }

/-- `campaignPreElection`'s request to `dst` (`MsgPreVote` at the next term, with the
last entry id), as `send` queues it. -/
def prevoteReq (id dst term : w64) (last : entryID) : Msg :=
  Msg.mk .preVote id dst term false last.index' last.term' (W64 0) (W64 0) []

/-- What `campaign(t)` leaves, with `pre` whether `t` is `campaignPreElection`: the role
transition, then the self-addressed response and one request per peer in `peers`,
each carrying the log's last entry id. An election is `becomeCandidate` and `MsgVote`s
at the new term; a pre-election is `becomePrecandidate` and `MsgPreVote`s at `Term + 1`
(the term itself does not move). The requests of an election carry the `Context` `cl`
(2026-10-13): `transferCtx t`, the marker for a leader transfer's campaign. -/
def campaignState (id : w64) (s : NState) (pre : Bool) (peers : List w64)
    (cl : List w8 := []) : NState :=
  if pre then
    sendMsgs (becomePrecandidate s)
      ([Msg.plain .preVoteResp id id (s.term + W64 1) false] ++
       peers.map fun dst => prevoteReq id dst (s.term + W64 1)
                 (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents)))
  else
    sendMsgs (becomeCandidate id s)
      ([Msg.plain .voteResp id id (becomeCandidate id s).term false] ++
       peers.map fun dst => pvoteReq id dst (becomeCandidate id s).term
                 (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents)) cl)

/-- `becomeLeader` up to its `appendEntry`: what `reset`, the `lead` and `state` writes
and `r.step` leave. -/
def becomeLeaderPre (id : w64) (s : NState) : NState :=
  { resetTo s s.term with lead := id, role := .leader, stepfn := stepFuncOf .leader,
                          ticking := true }

/-- The empty entry a new leader appends (`pb.Entry{Data: nil}`, the zero `Entry`),
stamped at the leader's term and the log's next index. -/
def leaderEntry (s : NState) : EntryM :=
  stamp s.term (logLast s.logst) 0 (zero_val EntryM)

/-- `appendEntry`'s self-acknowledgement, at a state whose log already holds the
appended batch: a `MsgAppResp` to itself at the last index (`r.send(pb.Message{To:
r.id, Type: pb.MsgAppResp, Index: li})`, with `li` what `raftLog.append` returned).
Visible in the abstract outbox since 2026-10-01. -/
def selfAck (id : w64) (s : NState) : Msg :=
  Msg.mk .appResp id id s.term false (logLast s.logst) (W64 0) (W64 0) (W64 0) []

/-- `becomeLeader` up to `appendEntry`'s `send`: `becomeLeaderPre`, `pendingConfIndex` at
the last index (2026-10-13), then the empty entry appended. -/
def becomeLeaderLog (id : w64) (s : NState) : NState :=
  { becomeLeaderPre id s with pci := logLast s.logst,
                              logst := logAppend s.logst [leaderEntry s] }

/-- `becomeLeader`: the empty entry appended and self-acknowledged. -/
def becomeLeader (id : w64) (s : NState) : NState :=
  sendMsgs (becomeLeaderLog id s) [selfAck id (becomeLeaderLog id s)]

/-! ### The connection to the protocol state -/

/-- Each peer's `Progress.Match`. -/
def prvalsMatch (pvs : GMap w64 Progress) : GMap w64 w64 :=
  Progress.matched <$> pvs

/-- Writing one peer's `Progress` without moving its `Match`. -/
theorem prvalsMatch_insert_same (pvs : GMap w64 Progress) (i : w64) (p p' : Progress)
    (Hi : pvs !! i = some p) (Hm : p'.matched = p.matched) :
    prvalsMatch (<[i := p']> pvs) = prvalsMatch pvs := by
  apply GMap.map_eq; intro k
  simp only [prvalsMatch, GMap.fmap_eq, GMap.lookup_fmap]
  by_cases hk : i = k
  · subst hk; rw [GMap.lookup_insert_eq, Hi]; simp [Hm]
  · rw [GMap.lookup_insert_ne _ _ hk]

/-- What `reset` leaves in `Match` (`raft.go:779-808`): `0` for every peer in the
progress map, then `lastIndex()` for the node itself. -/
def resetMatched (id li : w64) (pvs : GMap w64 Progress) : GMap w64 w64 :=
  GMap.imap (fun k _ => some (if k = id then li else W64 0)) pvs

/-- `reset`'s `Match` values are what `Step.win` asks of a new leader, when the node is
in the progress map. -/
theorem resetMatched_leader_ok (id : w64) (s : NState) (Hid : id ∈ domSet s.prvals)
    (ps : PState) (Hb : ps.base = s.logst.prev) (Hl : ps.log = s.logst.sents ++ s.logst.uents) :
    LeaderMatchOk id ps (resetMatched id (logLast s.logst) s.prvals) := by
  constructor
  · have Hid' : (s.prvals !! id).isSome := by
      simpa [domSet, GMap.mem_iff] using Hid
    obtain ⟨p, Hp⟩ := Option.isSome_iff_exists.1 Hid'
    rw [resetMatched, GMap.lookup_imap, Hp]
    simp only [Option.bind_some, ↓reduceIte, Option.some.injEq]
    simp only [plastIndex, plogLastIndexZ, logLast, Hb, Hl, List.length_append]
    congr 1; push_cast; omega
  · intro v x Hne
    rw [resetMatched, GMap.lookup_imap]
    cases s.prvals !! v with
    | none => simp
    | some _ => simp [Hne]; exact fun h => h.symm

/-- `matched` is `Match` for a leader and `∅` otherwise (`PState`): a non-leader's
`Progress` values are whatever its last `reset` left, and no rule reads them. This is
what lets every non-leader spec leave the `Progress` values unconstrained.

A pre-candidate (2026-10-04) is a follower with no leader and an empty tally: the
pre-vote tally in `trk.Votes` is invisible to the protocol
(notes/raft-replication-model.md, "Phase 3 ... Pre-vote"). Its physical `lead` is `0`
too (`becomePreCandidate` sets it, and nothing writes it while the role lasts), but
that is not recorded, so the reading does not depend on it. `prevote` is invisible. -/
def toPState (s : NState) : PState where
  term := s.term
  vote := s.vote
  lead := if s.role = .preCandidate then W64 0 else s.lead
  role := proleRole s.role
  votes := if s.role = .preCandidate then ∅ else s.votes
  outbox := s.outbox
  base := s.logst.prev
  log := s.logst.sents ++ s.logst.uents
  commit := s.logst.committed
  matched := if s.role = .leader then prvalsMatch s.prvals else ∅
  -- (2026-10-12) a non-leader's read-only object is the fresh one `reset` installed
  rd := if s.role = .leader then s.rd else rdNL s.rd

/-- A physical state that can take a protocol step: `r.step` agrees with the role, and
`r.tick` is set (2026-10-09).
Every `becomeX` establishes it. -/
def NStateWf (s : NState) : Prop := s.stepfn = stepFuncOf s.role ∧ s.ticking = true

/-- `s` refines the protocol state `ps`. -/
def NStateRel (s : NState) (ps : PState) : Prop := toPState s = ps ∧ NStateWf s

/-- What `maybeSendAppend` and its callers may send, at the state `s` they were called
in: `ReplOk` (`Protocol/Model.lean`) of the protocol reading of `s`. Replaced
`AppSends` on 2026-10-01. (2026-10-14, reconfiguration stage B7) and an `MsgApp` carries the
sender's commit index exactly (`AppCommitEq`: `sendAppend`'s `Commit: r.raftLog.committed`),
which the dynamic model's `StepR.sendApps`/`win` require (stage B3's finding: I1 fails for an
`MsgApp` with an older commit index). -/
def ReplSends (id : w64) (s : NState) (ms : List Msg) : Prop :=
  ∀ m ∈ ms, ReplOk id (toPState s) m ∧ AppCommitEq (toPState s) m ∧
    -- (D19p, 2026-10-18) a snapshot goes to a peer of the progress map (`maybeSendSnapshot`'s
    -- `pr`)
    (m.ty = .snap → m.dst ∈ domSet s.progress) ∧
    -- (2026-10-19, D21 M3) and never in the no-snapshot mode (`NGhost.ns`): there `Next ≥ 2`
    -- and the storage is never compacted past `1`, so `maybeSendAppend` never falls back to one
    (m.ty = .snap → s.gh.ns = false)

/-- The `ReplOk` half of `ReplSends`: what `StepC.sendApps` takes. -/
theorem ReplSends.replOk {id : w64} {s : NState} {ms : List Msg} (H : ReplSends id s ms) :
    ∀ m ∈ ms, ReplOk id (toPState s) m :=
  fun m hm => (H m hm).1

/-- The `AppCommitEq` part of `ReplSends`. -/
theorem ReplSends.commitEq {id : w64} {s : NState} {ms : List Msg} (H : ReplSends id s ms) :
    ∀ m ∈ ms, AppCommitEq (toPState s) m :=
  fun m hm => (H m hm).2.1

/-- (D19p) The snapshot part of `ReplSends`, at a configuration `c` tracking the progress map. -/
theorem ReplSends.snapTo {id : w64} {s : NState} {ms : List Msg} (H : ReplSends id s ms)
    {c : CfgM} (Hc : domSet s.progress ⊆ c.voters ∪ c.learners) :
    ∀ m ∈ ms, m.ty = .snap → m.dst ∈ c.voters ∪ c.learners :=
  fun m hm hs => (GMap.elem_of_subseteq _ _).1 Hc _ ((H m hm).2.2.1 hs)

/-! Each physical transition is its protocol counterpart on `toPState`. Stated so that
proofs rewrite rather than unfold. -/

theorem toPState_sendMsgs (s : NState) (ms : List Msg) :
    toPState (sendMsgs s ms) = psendMsgs (toPState s) ms := rfl

/-- The protocol reading's read state, with the read-only object reset (2026-10-12). -/
theorem rdNL_toPState (s : NState) : rdNL (toPState s).rd = rdNL s.rd := by
  by_cases h : s.role = .leader <;> simp [toPState, h, rdNL]

theorem toPState_becomeFollower (s : NState) (term lead : w64) :
    toPState (becomeFollower s term lead) = pbecomeFollower (toPState s) term lead := by
  have h := rdNL_toPState s
  unfold toPState becomeFollower resetTo resetTo0 pbecomeFollower at *
  simp only at *
  rw [h]; rfl

/-- `reset`'s conditional clear of the vote is overwritten by `vote := id`. -/
theorem toPState_becomeCandidate (id : w64) (s : NState) :
    toPState (becomeCandidate id s) = pbecomeCandidate id (toPState s) := by
  have h := rdNL_toPState s
  unfold toPState becomeCandidate resetTo resetTo0 pbecomeCandidate at *
  simp only at *
  rw [h]; rfl

/-- `lastIndex()` as the two layers write it. -/
theorem plastIndex_toPState (s : NState) : plastIndex (toPState s) = logLast s.logst := by
  simp only [plastIndex, plogLastIndexZ, logLast, toPState, List.length_append]
  congr 1; push_cast; omega

theorem leaderEntry_toPState (s : NState) : leaderEntry s = pleaderEntry (toPState s) := by
  rw [leaderEntry, pleaderEntry, plastIndex_toPState]; rfl

/-- `becomeLeader`, with the `Progress` values `reset` left: the protocol's win, up to
its broadcast. -/
theorem toPState_becomeLeader (id : w64) (s : NState) (pvs : GMap w64 Progress) :
    toPState { becomeLeader id s with prvals := pvs } =
      psendMsgs (pwinState id (toPState s) (prvalsMatch pvs))
        [pselfAck id (pwinState id (toPState s) (prvalsMatch pvs))] := by
  have Hw : toPState { becomeLeaderLog id s with prvals := pvs } =
      pwinState id (toPState s) (prvalsMatch pvs) := by
    simp only [becomeLeaderLog, becomeLeaderPre, resetTo, resetTo0, toPState, pwinState, pappend,
      pbecomeLeader, logAppend, leaderEntry_toPState, List.append_assoc, ite_true, rdNL_ite]
    rfl
  rw [← Hw]
  simp only [becomeLeader, pselfAck, sendMsgs, psendMsgs]
  have Hl := plastIndex_toPState { becomeLeaderLog id s with prvals := pvs }
  rw [Hl]
  rfl

theorem toPState_votes (s : NState) (v : GMap w64 Bool) (Hr : s.role ≠ .preCandidate) :
    toPState { s with votes := v } = { toPState s with votes := v } := by
  simp [toPState, Hr]

/-- A pre-candidate's tally is invisible. -/
theorem toPState_votes_pre (s : NState) (v : GMap w64 Bool) (Hr : s.role = .preCandidate) :
    toPState { s with votes := v } = toPState s := by
  simp [toPState, Hr]

/-- `becomePreCandidate` is, protocol-wise, a step down to a follower with no leader at
the same term: the vote is kept, the tally cleared. -/
theorem toPState_becomePrecandidate (s : NState) :
    toPState (becomePrecandidate s) = pbecomeFollower (toPState s) s.term (W64 0) := by
  by_cases h : s.role = .leader <;>
    simp [toPState, becomePrecandidate, pbecomeFollower, proleRole, h, rdNL]

/-- The protocol's reading of the role, the leader and a follower's tally. -/
theorem toPState_role (s : NState) : (toPState s).role = proleRole s.role := rfl

theorem toPState_lead_0 (s : NState) (Hl : s.lead = W64 0) : (toPState s).lead = W64 0 := by
  simp only [toPState]; split <;> simp_all

theorem toPState_lead_nonpre (s : NState) (Hr : s.role ≠ .preCandidate) :
    (toPState s).lead = s.lead := by
  simp [toPState, Hr]

theorem toPState_votes_nonpre (s : NState) (Hr : s.role ≠ .preCandidate) :
    (toPState s).votes = s.votes := by
  simp [toPState, Hr]

/-- `FollowerVotesOk` of the protocol reading, for the physical role. -/
theorem followerVotesOk_phys (s : NState) (Hfv : FollowerVotesOk (toPState s))
    (Hr : s.role = .follower) : s.votes = ∅ := by
  have Hrole : (toPState s).role = .follower := by simp [toPState, Hr, proleRole]
  have := Hfv Hrole
  simpa [toPState, Hr] using this

theorem toPState_vote (s : NState) (v : w64) :
    toPState { s with vote := v } = { toPState s with vote := v } := rfl

theorem nstateWf_becomeFollower (s : NState) (term lead : w64) :
    NStateWf (becomeFollower s term lead) := ⟨rfl, rfl⟩

theorem nstateWf_becomeCandidate (id : w64) (s : NState) :
    NStateWf (becomeCandidate id s) := ⟨rfl, rfl⟩

theorem nstateWf_becomeLeader (id : w64) (s : NState) : NStateWf (becomeLeader id s) :=
  ⟨rfl, rfl⟩

theorem nstateWf_becomePrecandidate (s : NState) : NStateWf (becomePrecandidate s) :=
  ⟨rfl, rfl⟩

/-- A state with new `Progress` values is as well-formed as before: `r.step` and the
role are untouched. -/
theorem nstateWf_prvals (s : NState) (pvs : GMap w64 Progress) (H : NStateWf s) :
    NStateWf { s with prvals := pvs } := H

/-- New `Progress` values are invisible to the protocol unless the node is leader and
`Match` moved. -/
theorem toPState_prvals (s : NState) (pvs : GMap w64 Progress)
    (H : s.role = .leader → prvalsMatch pvs = prvalsMatch s.prvals) :
    toPState { s with prvals := pvs } = toPState s := by
  by_cases Hr : s.role = .leader
  · simp [toPState, Hr, H Hr]
  · simp [toPState, Hr]

/-- The common case: a non-leader. -/
theorem toPState_prvals_nl (s : NState) (pvs : GMap w64 Progress) (Hr : s.role ≠ .leader) :
    toPState { s with prvals := pvs } = toPState s :=
  toPState_prvals s pvs (fun h => absurd h Hr)

theorem nstateWf_sendMsgs (s : NState) (ms : List Msg) (H : NStateWf s) :
    NStateWf (sendMsgs s ms) := H

/-- `ReplOk` reads only the term, the log and the commit index. -/
theorem replOk_proper (id : w64) (ps ps' : PState) (m : Msg)
    (Ht : ps'.term = ps.term) (Hb : ps'.base = ps.base) (Hl : ps'.log = ps.log)
    (Hc : ps'.commit = ps.commit) (H : ReplOk id ps m) : ReplOk id ps' m := by
  unfold ReplOk AppOk SnapOk at *
  rw [Ht, Hb, Hl, Hc]; exact H

/-- `replOk_proper` for `ReplSends`'s element (with `AppCommitEq`, 2026-10-14). -/
theorem replAC_proper (id : w64) (ps ps' : PState) (m : Msg)
    (Ht : ps'.term = ps.term) (Hb : ps'.base = ps.base) (Hl : ps'.log = ps.log)
    (Hc : ps'.commit = ps.commit) (H : ReplOk id ps m ∧ AppCommitEq ps m) :
    ReplOk id ps' m ∧ AppCommitEq ps' m :=
  ⟨replOk_proper id ps ps' m Ht Hb Hl Hc H.1, fun h => by rw [Hc]; exact H.2 h⟩

/-- `replAC_proper` for `ReplSends`'s element (D19p: with the snapshot's peer), at a state with
the same progress map. -/
theorem replACS_proper (id : w64) (s s' : NState) (m : Msg)
    (Ht : (toPState s').term = (toPState s).term) (Hb : (toPState s').base = (toPState s).base)
    (Hl : (toPState s').log = (toPState s).log) (Hc : (toPState s').commit = (toPState s).commit)
    (Hp : s'.progress = s.progress)
    (H : ReplOk id (toPState s) m ∧ AppCommitEq (toPState s) m ∧
      (m.ty = .snap → m.dst ∈ domSet s.progress) ∧ (m.ty = .snap → s.gh.ns = false))
    (Hg : s'.gh.ns = s.gh.ns) :
    ReplOk id (toPState s') m ∧ AppCommitEq (toPState s') m ∧
      (m.ty = .snap → m.dst ∈ domSet s'.progress) ∧ (m.ty = .snap → s'.gh.ns = false) :=
  ⟨replOk_proper id _ _ m Ht Hb Hl Hc H.1, fun h => by rw [Hc]; exact H.2.1 h,
    fun h => by rw [Hp]; exact H.2.2.1 h, fun h => by rw [Hg]; exact H.2.2.2 h⟩

theorem replSends_prvals (id : w64) (s : NState) (pvs : GMap w64 Progress) (ms : List Msg) :
    ReplSends id { s with prvals := pvs } ms ↔ ReplSends id s ms := by
  unfold ReplSends
  constructor <;> intro H m Hm <;>
    exact ⟨replOk_proper _ _ _ _ rfl rfl rfl rfl (H m Hm).1, (H m Hm).2.1, (H m Hm).2.2⟩

theorem replSends_app (id : w64) (s : NState) (ms1 ms2 : List Msg)
    (H1 : ReplSends id s ms1) (H2 : ReplSends id s ms2) : ReplSends id s (ms1 ++ ms2) := by
  intro m Hm
  rcases List.mem_append.1 Hm with h | h
  · exact H1 m h
  · exact H2 m h

/-- Sending messages, or changing `Progress` values, does not change what `ReplOk`
reads. -/
theorem replSends_send_prvals (id : w64) (s : NState) (ms0 : List Msg)
    (pvs : GMap w64 Progress) (ms : List Msg) :
    ReplSends id { sendMsgs s ms0 with prvals := pvs } ms ↔ ReplSends id s ms := by
  unfold ReplSends
  constructor <;> intro H m Hm <;>
    exact ⟨replOk_proper _ _ _ _ rfl rfl rfl rfl (H m Hm).1, (H m Hm).2.1, (H m Hm).2.2⟩

end phys_state

end EtcdGrove
end Perennial

-- Projection lemmas, `@[simp, word_unfold]` (ProjSimps.lean).
proj_simps Perennial.EtcdGrove.inflightsAbs Perennial.EtcdGrove.inflightsReset Perennial.EtcdGrove.inflightsAdd Perennial.EtcdGrove.inflightsNew Perennial.EtcdGrove.progressResetState Perennial.EtcdGrove.progressBecomeProbe Perennial.EtcdGrove.progressBecomeReplicate Perennial.EtcdGrove.progressBecomeSnapshot Perennial.EtcdGrove.progressSentCommit Perennial.EtcdGrove.logAppend Perennial.EtcdGrove.logRestore Perennial.EtcdGrove.sendMsgs Perennial.EtcdGrove.resetTo Perennial.EtcdGrove.becomeFollower Perennial.EtcdGrove.becomeCandidate Perennial.EtcdGrove.becomePrecandidate Perennial.EtcdGrove.becomeLeaderPre Perennial.EtcdGrove.becomeLeaderLog
