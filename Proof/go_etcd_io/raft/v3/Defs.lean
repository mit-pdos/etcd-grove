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
def absMsgFrom (ty : MsgType) (m : raftpb.Message) (src term : w64)
    (ents : List raftpb.Entry) : Msg :=
  Msg.mk ty src m.To' term m.Reject' m.Index' m.LogTerm' m.Commit' m.RejectHint' ents

/-- The abstraction of a physical message. Not a function of `m` alone: `m.Entries` is
a slice, and `ents` is the list it points to -- `ownRaftPhys` holds `m.Entries ↦*□ ents`
for every queued message (`outboxRel`, `InvRaftPhys.lean`). Not for a `MsgSnap`: see
`absSnap`. -/
def absMsg (ty : MsgType) (m : raftpb.Message) (ents : List raftpb.Entry) : Msg :=
  absMsgFrom ty m m.From' m.Term' ents

/-- The abstraction of a `MsgSnap` (2026-10-02). What the protocol reads of a snapshot
is behind the pointer `m.Snapshot`: `sv` is the `Snapshot` it points to, and `voters`
the list behind `sv`'s `Metadata.ConfState.Voters` slice. `index`/`logterm` are the
snapshot's `Metadata.Index`/`Metadata.Term` -- not `m`'s own `Index`/`LogTerm`, which
`maybeSendSnapshot` leaves at `0` -- and there are no entries. As for `absMsgFrom`,
`src`/`term` are given separately because `send` stamps them. -/
def absSnapFrom (m : raftpb.Message) (src term : w64) (sv : raftpb.Snapshot)
    (voters : List w64) : Msg :=
  Msg.mkV .snap src m.To' term m.Reject' sv.Metadata'.Index' sv.Metadata'.Term'
    m.Commit' m.RejectHint' [] voters

def absSnap (m : raftpb.Message) (sv : raftpb.Snapshot) (voters : List w64) : Msg :=
  absSnapFrom m m.From' m.Term' sv voters

end msgs

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
  sents : List raftpb.Entry
  uents : List raftpb.Entry
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
  (`InvRaftlog.lean`, `Hpersist`, `StorApp`). The application appends them through
  `ownRaftLog_persist`, which empties the field; `Advance` requires it empty. -/
  unpersisted : List raftpb.Entry
  /-- What the `Storage` holds (its entries after `prev`) once the application has
  appended `unpersisted` (2026-10-10), while no snapshot is pending (`InvRaftlog.lean`,
  `Hstored`): ghost, not a Go field. Only a `Ready` changes it (`logAcceptUnstable`: the
  whole log, which the storage holds once the entries handed out are appended); a
  truncating `MsgApp` leaves it, so after one the storage may hold entries the log no
  longer has. `stableTo` needs it (`StableOk`, `InvReadylog.lean`): an acknowledgement
  `Advance` steps after a truncation is right only because the storage still agrees
  with the log up to the acknowledged entry. -/
  stored : List raftpb.Entry
  /-- `l.applyingEntsSize` and `l.maxApplyingEntsSize` (2026-10-05): the flow control
  on handing out committed entries. In the state because `acceptApplying` calls
  `maxAppliableIndex` between updating the size and the paused flag, and only what the
  state records survives that call (`ownRaftLog`'s `Hpaused` needs the size to be
  under the limit while applying is not paused). -/
  apsize : w64
  apmax : w64

/-! ## The tracker's records (2026-10-02)

The public representation predicates of the tracker side -- `ownInflights l i`,
`ownProgress pr p` and `ownTracker cfg tv t` (`InvTracker.lean`) -- are indexed by
these records rather than by the Goose struct types: each holds exactly the state the
exported methods' specs need (notes/raft-replication-model.md, "Public representation
predicates"). They live here and not in `InvTracker.lean` because `NState.prvals`
below is a map of `Progress`, and `InvTracker.lean` builds on this file -- the same
reason `LogState` is here. -/

/-- Go's `min`/`max` builtins on `uint64`, exactly as Goose's `minⁱᵐᵖˡ`/`maxⁱᵐᵖˡ`
compute them: `min x y = if x < y then x else y`, `max x y = if x > y then x else y`
(and Goose renders `x > y` as `y < x`). Stated with `decide`, the form of the
framework's `wp_max2_uint64`. (Moved here from `InvTracker.lean` with the `Progress`
methods.) -/
def w64Min (x y : w64) : w64 := if uint.Z x < uint.Z y then x else y
def w64Max (x y : w64) : w64 := if uint.Z y < uint.Z x then x else y

theorem w64Min_spec (x y : w64) : uint.Z (w64Min x y) = min (uint.Z x) (uint.Z y) := by
  unfold w64Min; split <;> omega

theorem w64Max_spec (x y : w64) : uint.Z (w64Max x y) = max (uint.Z x) (uint.Z y) := by
  unfold w64Max; split <;> omega

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

/-- A `Progress`, without `IsLearner` (no learners are in scope: the abstraction
function below is undefined on one) and with the state an inductive. `paused` is
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

/-- `none` on a learner and on a state outside the three: what the two pure conjuncts
of `ownProgress` used to rule out. -/
def progressAbs (pv : tracker.Progress) (i : Inflights) : Option Progress :=
  if pv.IsLearner' then none else
  (prstateOfW64 pv.State').map fun st =>
    ⟨pv.Match', pv.Next', pv.sentCommit', st, pv.PendingSnapshot', pv.MsgAppFlowPaused', i⟩

/-- What `progressAbs pv i = some p` says, field by field. -/
theorem progressAbs_Some (pv : tracker.Progress) (i : Inflights) (p : Progress) :
    progressAbs pv i = some p ↔
    pv.IsLearner' = false ∧
    pv.State' = prstateW64 p.state ∧
    pv.Match' = p.matched ∧
    pv.Next' = p.next ∧
    pv.sentCommit' = p.sentCommit ∧
    pv.PendingSnapshot' = p.pendingSnapshot ∧
    pv.MsgAppFlowPaused' = p.paused ∧
    i = p.infl := by
  unfold progressAbs
  obtain ⟨m, n, sc, st, ps, pa, inf⟩ := p
  cases hl : pv.IsLearner'
  · simp only [Bool.false_eq_true, ↓reduceIte, true_and]
    rw [← prstateOfW64_Some]
    cases hs : prstateOfW64 pv.State' with
    | none => simp
    | some st' =>
      simp only [Option.map_some, Option.some.injEq, Progress.mk.injEq]
      constructor
      · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
        exact ⟨h4 ▸ rfl, h1, h2, h3, h5, h6, h7⟩
      · rintro ⟨h4, h1, h2, h3, h5, h6, h7⟩
        exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  · simp

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

section logstate
variable [FfiSyntax]

/-! ## Physical transitions of the log

`logLast ls` is `lastIndex()` of a log at `ls`, as a `w64`; the `raftLog` specs return
it as an `Int` equation, and `ownRaftLog`'s `Hnowrap` says the `W64` does not wrap. -/

def logLast (ls : LogState) : w64 :=
  W64 (uint.Z ls.prev.index' + ls.sents.length + ls.uents.length)

/-- `raftLog.append` at the end of the log: the batch joins the unstable suffix
(`Spec/raftLog__append.lean`). -/
def logAppend (ls : LogState) (ents : List raftpb.Entry) : LogState :=
  { ls with uents := ls.uents ++ ents }

/-- A snapshot's id, `(Metadata.Term, Metadata.Index)` -- what `raft.restore` builds as
`id := entryID{term, index}`. -/
def snapId (sv : raftpb.Snapshot) : entryID :=
  entryID.mk sv.Metadata'.Term' sv.Metadata'.Index'

/-- `raftLog.restore(s)` (`Spec/raftLog__restore.lean`): the log is the snapshot -- its
id is the boundary, nothing after it, committed up to it, `applied` untouched, the
snapshot pending. `unstable.restore` sets `offsetInProgress` to the new offset;
`applying` and the unpersisted entries are untouched. -/
def logRestore (ls : LogState) (sid : entryID) : LogState :=
  ⟨sid, [], [], sid.index', ls.applied, some sid, sid.index' + W64 1, ls.applying,
   ls.unpersisted, ls.stored, ls.apsize, ls.apmax⟩

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
def resetTo (s : NState) (term : w64) : NState :=
  { s with term := term, vote := if term = s.term then s.vote else W64 0, lead := W64 0,
           votes := ∅ }

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
(the term itself does not move). -/
def campaignState (id : w64) (s : NState) (pre : Bool) (peers : List w64) : NState :=
  if pre then
    sendMsgs (becomePrecandidate s)
      ([Msg.plain .preVoteResp id id (s.term + W64 1) false] ++
       peers.map fun dst => prevoteReq id dst (s.term + W64 1)
                 (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents)))
  else
    sendMsgs (becomeCandidate id s)
      ([Msg.plain .voteResp id id (becomeCandidate id s).term false] ++
       peers.map fun dst => pvoteReq id dst (becomeCandidate id s).term
                 (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents)))

/-- `becomeLeader` up to its `appendEntry`: what `reset`, the `lead` and `state` writes
and `r.step` leave. -/
def becomeLeaderPre (id : w64) (s : NState) : NState :=
  { resetTo s s.term with lead := id, role := .leader, stepfn := stepFuncOf .leader,
                          ticking := true }

/-- The empty entry a new leader appends (`pb.Entry{Data: nil}`, the zero `Entry`),
stamped at the leader's term and the log's next index. -/
def leaderEntry (s : NState) : raftpb.Entry :=
  stamp s.term (logLast s.logst) 0 (zero_val raftpb.Entry)

/-- `appendEntry`'s self-acknowledgement, at a state whose log already holds the
appended batch: a `MsgAppResp` to itself at the last index (`r.send(pb.Message{To:
r.id, Type: pb.MsgAppResp, Index: li})`, with `li` what `raftLog.append` returned).
Visible in the abstract outbox since 2026-10-01. -/
def selfAck (id : w64) (s : NState) : Msg :=
  Msg.mk .appResp id id s.term false (logLast s.logst) (W64 0) (W64 0) (W64 0) []

/-- `becomeLeader` up to `appendEntry`'s `send`: `becomeLeaderPre`, then the empty
entry appended. -/
def becomeLeaderLog (id : w64) (s : NState) : NState :=
  { becomeLeaderPre id s with logst := logAppend s.logst [leaderEntry s] }

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

/-- A physical state that can take a protocol step: `r.step` agrees with the role, and
`r.tick` is set (2026-10-09).
Every `becomeX` establishes it. -/
def NStateWf (s : NState) : Prop := s.stepfn = stepFuncOf s.role ∧ s.ticking = true

/-- `s` refines the protocol state `ps`. -/
def NStateRel (s : NState) (ps : PState) : Prop := toPState s = ps ∧ NStateWf s

/-- What `maybeSendAppend` and its callers may send, at the state `s` they were called
in: `ReplOk` (`Protocol/Model.lean`) of the protocol reading of `s`. Replaced
`AppSends` on 2026-10-01. -/
def ReplSends (id : w64) (s : NState) (ms : List Msg) : Prop :=
  ∀ m ∈ ms, ReplOk id (toPState s) m

/-! Each physical transition is its protocol counterpart on `toPState`. Stated so that
proofs rewrite rather than unfold. -/

theorem toPState_sendMsgs (s : NState) (ms : List Msg) :
    toPState (sendMsgs s ms) = psendMsgs (toPState s) ms := rfl

theorem toPState_becomeFollower (s : NState) (term lead : w64) :
    toPState (becomeFollower s term lead) = pbecomeFollower (toPState s) term lead := rfl

/-- `reset`'s conditional clear of the vote is overwritten by `vote := id`. -/
theorem toPState_becomeCandidate (id : w64) (s : NState) :
    toPState (becomeCandidate id s) = pbecomeCandidate id (toPState s) := rfl

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
    simp only [becomeLeaderLog, becomeLeaderPre, resetTo, toPState, pwinState, pappend,
      pbecomeLeader, logAppend, leaderEntry_toPState, List.append_assoc, ite_true]
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
  simp [toPState, becomePrecandidate, pbecomeFollower, proleRole]

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

theorem replSends_prvals (id : w64) (s : NState) (pvs : GMap w64 Progress) (ms : List Msg) :
    ReplSends id { s with prvals := pvs } ms ↔ ReplSends id s ms := by
  unfold ReplSends
  constructor <;> intro H m Hm <;> exact replOk_proper _ _ _ _ rfl rfl rfl rfl (H m Hm)

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
  constructor <;> intro H m Hm <;> exact replOk_proper _ _ _ _ rfl rfl rfl rfl (H m Hm)

end phys_state

end EtcdGrove
end Perennial

-- Projection lemmas, `@[simp, word_unfold]` (ProjSimps.lean).
proj_simps Perennial.EtcdGrove.inflightsAbs Perennial.EtcdGrove.inflightsReset Perennial.EtcdGrove.inflightsAdd Perennial.EtcdGrove.inflightsNew Perennial.EtcdGrove.progressResetState Perennial.EtcdGrove.progressBecomeProbe Perennial.EtcdGrove.progressBecomeReplicate Perennial.EtcdGrove.progressBecomeSnapshot Perennial.EtcdGrove.progressSentCommit Perennial.EtcdGrove.logAppend Perennial.EtcdGrove.logRestore Perennial.EtcdGrove.sendMsgs Perennial.EtcdGrove.resetTo Perennial.EtcdGrove.becomeFollower Perennial.EtcdGrove.becomeCandidate Perennial.EtcdGrove.becomePrecandidate Perennial.EtcdGrove.becomeLeaderPre Perennial.EtcdGrove.becomeLeaderLog
