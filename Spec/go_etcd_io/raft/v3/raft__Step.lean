/- Port of election_proof/spec_raft__Step.v (857d09190).

Lean notes:
* The spec mentions ghost state (`ownRaftGhost`, `isMessage`), so the section has the extra variable `[AllG GF]` (porting guide,
  "Section variables"), and fixes `hlc := HasLC.hasLC` (`[hG : HeapGS HasLC.hasLC GF]`
  instead of `{hlc : HasLC} [hG : HeapGS hlc GF]`): `ownRaftGhost` (through
  `raftCommitInv`) needs `[InvGS GF]`, which is `InvGS_gen .hasLC GF`, and the heap's
  invariant instance is one only at `hlc = .hasLC` -- the convention of Perennial's
  ports that state specs with invariants (`v3_proof/protocol.lean`, `context.lean`).
  Rocq's `heapGS` always carries that instance, so this is the faithful reading; a
  separate `[InvGS GF]` variable would be an invariant world unrelated to the WP's.
  Specs stated generically in `hlc` (every callee's) instantiate at `.hasLC`.
* Rocq's `Require Export New.proof.bytes` (for `wp_Equal`, used by the `MsgVote`
  branch's `Context` comparison) is `import Perennial.Proof.bytes`. The Rocq file
  imports `spec_raft__restore` before `step_lemmas` so that the model's `step` wins over
  any other `step` in scope; in Lean the model relation is `Step` and there is no
  clash.
* Rocq's `step_msg_types`/`step_msg` are `stepMsgTypes`/`StepMsg`; stdpp's
  `list.last` is `List.getLast?`.
* The context's existential is typed `ctx : List w8` (Rocq infers it from `↦*□` and
  the comparison with the `go_string` `campaignTransfer`).
* `[∗ list] e;Q ∈ ents;Qs, …` is `bigSepL2`; Rocq's `word.add (word.add (plast_index
  ps) (W64 1)) (W64 k)` (`k : nat`) is `plastIndex ps + W64 1 + W64 (k : Int)`.

raft v3.7 (2026-10-15, stage R4; `notes/decisions.md`, "`raft.go` over pointer messages"): `Step`
takes a `*pb.Message` (`ml`) **for good** (Q3), as a received message: `msgIn ml dqe ⟨m, ents, sn,
ctx, rs⟩` -- the struct at `1` (`stepFollower` replaces `To`, `send` `From`/`Term`), the entry
pointers at `1` for a `MsgProp` (the conf-change loop replaces refused entries' slots) and
read-only otherwise, the `Entries` slice's capacity owned (a `MsgApp`'s array may be adopted), the
snapshot owned (`EnsureSnapshot`/`EnsureConfState`). The record's parts are quantified apart --
the scalars `m : MessageM`, the entries `ents`, the context `ctx`, the snapshot `sn`, the
responses `rs` -- so that every pure premise and abstraction keeps its text. `"Hents"`'s and
`"Hents_cap"`'s heap parts and `"#Hctx"` are `msgIn`'s; a proposal's conf-change entries' bytes
(`ccEntsOk`) stay (pure since D6: an entry's `Data'` is its bytes; phase 2 of R4 also took the
entries' data bytes, for `appendEntry`'s clones, which D6 made unneeded); the `MsgSnap` premise is on the snapshot the message holds (`sn = some sv`) and its
`ConfState`'s lists (`scfg = sv.Metadata'.ConfState'.lists`, until the retarget the read-only
slices, `ownCSL`); `MsgStorageAppendResp`'s `m.Snapshot' = null` is `sn = none`, and
`RestMsgOk`'s "`Entries`/`Context` `nil`" is `ents = []`/`ctx = []` (so it takes `ents`, `ctx`).
Nothing of the message is given back.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys
-- `StableOk`, for `MsgStorageAppendResp` (2026-10-05)
public import Proof.go_etcd_io.raft.v3.InvReadylog
public import Proof.go_etcd_io.raft.v3.InvConfChangeMsg
-- `SnapScope`, for `MsgSnap`
public import Spec.go_etcd_io.raft.v3.raft__restore
-- (2026-10-14, stage B7) the ghost modes
public import Proof.go_etcd_io.raft.v3.StepGhostMode
public import Proof.go_etcd_io.raft.v3.SnapRoleBack
public import Proof.go_etcd_io.raft.v3.StepLemmas
-- `MsgBeat`
public import Spec.go_etcd_io.raft.v3.raft__handleHeartbeat
-- `bytes.wp_Equal`, for the `MsgVote` branch's `Context` comparison.
public import Perennial.Proof.bytes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-- The message types `Step` is specified for: every type its branches cover
(2026-10-02; until then only `MsgHup`/`MsgVote`/`MsgVoteResp`, `ElectionMsg`;
`MsgPreVote`/`MsgPreVoteResp` since 2026-10-04; the two local storage acknowledgements
`RawNode.Advance` steps, `MsgStorageAppendResp`/`MsgStorageApplyResp`, since
2026-10-05; `MsgCheckQuorum` since 2026-10-17, with `CheckQuorum` on). -/
def stepMsgTypes : List w32 :=
  [MsgHup, MsgVote, MsgVoteResp, MsgApp, MsgAppResp, MsgHeartbeat,
   MsgHeartbeatResp, MsgBeat, MsgProp, MsgSnap, MsgPreVote, MsgPreVoteResp,
   MsgStorageAppendResp, MsgStorageApplyResp, MsgReadIndex, MsgReadIndexResp,
   MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTransferLeader, MsgTimeoutNow,
   MsgCheckQuorum]

/-- (2026-10-13) The premises of the types `Step` was extended to last: the local reports
(`ReportUnreachable`, `ReportSnapshot`) and `ForgetLeader` are unstamped (`Term = 0`);
a `MsgTimeoutNow` makes a follower campaign, at the message's term if it is later, so
neither term wraps; and a leader-transfer request stamped with a term (forwarded by a
follower to the leader it knew, `To: r.lead`) reaches a node that, at that term, is no
follower with a leader -- the leader it was sent to stays leader for the term, or (2026-10-17,
`checkQuorum` on) steps down at it to a follower with no leader, and no other node leads it -- since a follower would
forward it again and `send` panics on a stamped `MsgTransferLeader`; and it carries no
entries and no context (`RawNode.TransferLeader` builds it so, and forwarding keeps it); and
(2026-10-19, D21 M2r) only at a node with leader transfer on (`NGhost.xf = false`): with it
off no transferee is recorded, so no `MsgTimeoutNow` is sent.
These are transport premises, like the others: no message fact carries them
(`MsgTransferLeader` and `MsgTimeoutNow` are outside the model, `mtypeOf` is `none`). -/
def RestMsgOk [GooseExts] (s : NState) (m : MessageM) (ents : List EntryM) (ctx : List w8) :
    Prop :=
  ((m.Type' = MsgForgetLeader ∨ m.Type' = MsgUnreachable ∨ m.Type' = MsgSnapStatus) →
     m.Term' = W64 0) ∧
  -- (D19i part 1) and with the floor at most `applied` (`hup`'s)
  (m.Type' = MsgTimeoutNow → uint.Z s.term + 1 < 2 ^ 64 ∧ uint.Z m.Term' + 1 < 2 ^ 64 ∧
     uint.Z s.logst.fl ≤ uint.Z s.logst.applied) ∧
  (m.Type' = MsgTransferLeader →
     ents = [] ∧ ctx = [] ∧
     (m.Term' ≠ W64 0 → m.Term' = s.term → s.role = .follower → s.lead = W64 0) ∧
     -- (2026-10-19, D21 M2r) only with leader transfer on (`NGhost.xf`)
     s.gh.xf = false)

/-- `RestMsgOk` of a message of none of those types. -/
theorem RestMsgOk.of_ne [GooseExts] {s : NState} {m : MessageM} {ents : List EntryM}
    {ctx : List w8}
    (h : m.Type' ≠ MsgForgetLeader ∧ m.Type' ≠ MsgUnreachable ∧ m.Type' ≠ MsgSnapStatus ∧
      m.Type' ≠ MsgTimeoutNow ∧ m.Type' ≠ MsgTransferLeader) : RestMsgOk s m ents ctx :=
  ⟨fun h' => by rcases h' with h' | h' | h' <;> simp_all,
   fun h' => absurd h' h.2.2.2.1, fun h' => absurd h' h.2.2.2.2⟩

def StepMsg [GooseExts] (m : MessageM) : Prop :=
  m.Type' ∈ stepMsgTypes

/-! ### A snapshot's acknowledgement (D22 S-d2, 2026-10-21)

The acknowledgement `RawNode.Advance` steps after a `Ready` that handed out a snapshot carries
it (`newStorageAppendRespMsg`, `rawnode.go:266`: `Snapshot` set), and both arms of `Step` that
take a `MsgStorageAppendResp` apply it (`appliedSnap`, after the `stableTo` of the entries the
`Ready` also handed out, in the current-term arm). The application's receipt is absorbed before
the step (`ownRaftLog_absorb_snap`: the storage at the pending snapshot, `sat`); the arm opens
the `sapp` window from it (`ownRaftLog_sapp`). -/

/-- The log the acknowledgement's `stableTo` sees: with a snapshot acknowledged and the storage
at the pending snapshot, in the `sapp` window. -/
def ackLog [GooseExts] (ls : LogState) (sn : Option SnapshotM) : LogState :=
  match sn with
  | none => ls
  | some _ => if ls.sat then { ls with sapp := true } else ls

/-- The entry the acknowledgement's `stableTo` is called at, if it is: in the current-term arm
(`Term` `0` or the node's) with an `Index`. -/
def ackStableId [GooseExts] (m : MessageM) (t : w64) : Option entryID :=
  if (m.Term' = W64 0 ∨ m.Term' = t) ∧ m.Index' ≠ W64 0 then some ⟨m.LogTerm', m.Index'⟩
  else none

/-- The log after the acknowledgement of a snapshot `sv` at a node of term `t`: `stableTo` (if
called) in the `sapp` window, then `appliedSnap`'s `stableSnapTo` and `appliedTo`. -/
def ackSnapLog [GooseExts] (ls : LogState) (m : MessageM) (t : w64) (sv : SnapshotM) : LogState :=
  logAppliedTo
    (logStableSnap
      (match ackStableId m t with
       | some id => logStableTo (ackLog ls (some sv)) id
       | none => ackLog ls (some sv))
      sv.Metadata'.Index')
    sv.Metadata'.Index' (W64 0)

/-- What a `Step` of one of the messages `RawNode` steps itself leaves of the node's
physical state beyond the protocol (2026-10-09): the term, the entries a `Ready` handed
out that the application has not appended yet (`unpersisted`), the pending snapshot,
and `offsetInProgress`, which does not move back; and (2026-10-10) the log's boundary
and what the storage holds (`prev`, the ghost `stored`), which the `RawNode` predicate
keeps the records of for the acknowledgement `Advance` steps (`InvRawnode.lean`); and
the storage the log reads (`LogState.storage`, constant), which the `RawNode` predicate
names to its client (`RNState.storage`); and (2026-10-10) `r.preVote`. -/
def LocalFrame [GooseExts] (s s' : NState) : Prop :=
  s'.term = s.term ∧
  uint.Z s.logst.inprogress ≤ uint.Z s'.logst.inprogress ∧
  s'.logst.unpersisted = s.logst.unpersisted ∧
  s'.logst.snap = s.logst.snap ∧
  s'.logst.prev = s.logst.prev ∧
  s'.logst.stored = s.logst.stored ∧
  s'.logst.storage = s.logst.storage ∧
  s'.prevote = s.prevote ∧
  s'.gh = s.gh ∧
  -- (2026-10-17) and the role (`PreCandStep`)
  s'.role = s.role ∧
  -- (D19i part 1) the floor, and `applied` does not move back
  s'.logst.fl = s.logst.fl ∧ uint.Z s.logst.applied ≤ uint.Z s'.logst.applied

/-- `Step`'s postcondition for the three local messages `RawNode` steps -- a proposal
(`Propose`) and the two storage acknowledgements (`Advance`): `LocalFrame`, and
`applying` is unchanged -- a `MsgStorageApplyResp` moves it (`appliedTo`) only past
entries not yet handed out, so not when its last entry is at or below it. This is what
lets the `RawNode` predicate (`InvRawnode.lean`) keep its client-facing facts on the log
(the committed entries handed out so far, the unpersisted ones) across a `Step`.
Nothing is said for any other message type. -/
def LocalStepOk [GooseExts] (m : MessageM) (ents : List EntryM)
    (s s' : NState) : Prop :=
  (m.Type' = MsgProp ∨ m.Type' = MsgStorageAppendResp ∨ m.Type' = MsgStorageApplyResp) →
  LocalFrame s s' ∧
  ((m.Type' = MsgStorageApplyResp →
      ∀ e, ents.getLast? = some e → uint.Z e.Index' ≤ uint.Z s.logst.applying) →
   s'.logst.applying = s.logst.applying) ∧
  -- (D19i part 1) an apply acknowledgement moves `applied` up to its last entry
  (m.Type' = MsgStorageApplyResp →
      ∀ e, ents.getLast? = some e → uint.Z e.Index' ≤ uint.Z s'.logst.applied)

/-- What every `Step` but a `MsgSnap`'s and a `MsgStorageApplyResp`'s leaves of the log's
state beyond the protocol (2026-10-09): `applying` (only `appliedTo` moves it), the pending
snapshot (only `restore` sets one) and the entries a `Ready` handed out that the
application has not appended yet (only `ownRaftLog_absorb` empties them). This is what
the `RawNode` predicate needs to survive a `Step` of a message from the network
(`RawNode.Step`, `Tick`, `Campaign`). Unlike `LocalFrame`, it says nothing of the term or
of `offsetInProgress`, which a truncating `MsgApp` moves back. And (2026-10-10) the log's
boundary `prev` and what the storage holds (the ghost `stored`): no `Step` but a
`MsgSnap`'s restores, and only a `Ready` changes `stored`, so a truncating `MsgApp`
leaves the storage holding entries the log no longer has -- which is why the
acknowledgement `Advance` steps after it may still move them stable (`StableOk`). And
the storage the log reads (`LogState.storage`, constant). And (2026-10-10) `r.preVote`,
never written after `newRaft` (the `RawNode` predicate keeps it off in the dynamic mode). -/
def NetFrame [GooseExts] (s s' : NState) : Prop :=
  s'.logst.applying = s.logst.applying ∧
  s'.logst.snap = s.logst.snap ∧
  s'.logst.unpersisted = s.logst.unpersisted ∧
  s'.logst.prev = s.logst.prev ∧
  s'.logst.stored = s.logst.stored ∧
  s'.logst.storage = s.logst.storage ∧
  s'.prevote = s.prevote ∧
  s'.gh = s.gh ∧
  -- (D19i part 1) the floor, and `applied` does not move back
  s'.logst.fl = s.logst.fl ∧ uint.Z s.logst.applied ≤ uint.Z s'.logst.applied

/-- (2026-10-19, D21 M3) A frame keeps the no-snapshot mode; (D21 M2r) and leader transfer: the
ghost state's flags (`NGhost`), all of it. -/
theorem NetFrame.ns [GooseExts] {s s' : NState} (H : NetFrame s s') : s'.gh = s.gh :=
  H.2.2.2.2.2.2.2.1

theorem LocalFrame.ns [GooseExts] {s s' : NState} (H : LocalFrame s s') : s'.gh = s.gh :=
  H.2.2.2.2.2.2.2.2.1

/-- (D22 S-b′3) ... and the storage (`ghostRest`'s certificate link is of it). -/
theorem NetFrame.nsst [GooseExts] {s s' : NState} (H : NetFrame s s') :
    s'.gh = s.gh ∧ s'.logst.storage = s.logst.storage :=
  ⟨H.ns, H.2.2.2.2.2.1⟩

theorem LocalFrame.nsst [GooseExts] {s s' : NState} (H : LocalFrame s s') :
    s'.gh = s.gh ∧ s'.logst.storage = s.logst.storage :=
  ⟨H.ns, H.2.2.2.2.2.2.1⟩

theorem NetFrame.refl [GooseExts] (s : NState) : NetFrame s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Int.le_refl _⟩

theorem NetFrame.trans [GooseExts] {s1 s2 s3 : NState} (h1 : NetFrame s1 s2)
    (h2 : NetFrame s2 s3) : NetFrame s1 s3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1,
   h2.2.2.2.2.1.trans h1.2.2.2.2.1, h2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.1, h2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.1, Int.le_trans h1.2.2.2.2.2.2.2.2.2 h2.2.2.2.2.2.2.2.2.2⟩

/-- Two states with the same log state and pre-vote setting. -/
theorem NetFrame.of_logst [GooseExts] {s s' : NState} (h : s'.logst = s.logst)
    (hpv : s'.prevote = s.prevote := by rfl) (hg : s'.gh = s.gh := by rfl) :
    NetFrame s s' := by
  unfold NetFrame; rw [h, hpv, hg]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Int.le_refl _⟩

/-- How a `Step` moves the term (2026-10-09): never back; by a local `MsgHup` at most one
up (a campaign); by any other message (but a `MsgPreVoteResp` or (2026-10-13) a
`MsgTimeoutNow`, which may also campaign) at most to the message's term. And
`offsetInProgress` does not move back but by a `MsgApp`, whose append may truncate the
in-progress entries. And (2026-10-13, for `node.go`'s term budget) a `MsgTimeoutNow` at most
one past the larger of the node's and the message's term: a step-down to the message's
term, then a campaign. And (2026-10-17, for the pre-candidate's budget at the `RawNode` layer)
a node that is a pre-candidate afterwards was one before, or stepped a `MsgHup` (a pre-campaign),
and is at the same term (`PreCandStep`). -/
def PreKeep [GooseExts] (s s' : NState) : Prop :=
  s'.logst.prev = s.logst.prev ∧ s'.logst.sents ++ s'.logst.uents = s.logst.sents ++ s.logst.uents ∧
  s'.logst.committed = s.logst.committed ∧ (s.logst.snap = none → s'.logst.snap = none) ∧
  uint.Z s.logst.applied ≤ uint.Z s'.logst.applied

/-- (2026-10-25, T-M M2b) What `hup` checked when it made the node a pre-candidate (`HupGuard`):
the log unchanged, no snapshot pending, no conf entry committed and not applied, and the log
facts that make that check `StepR.campaign`'s guard on the full log (`noConfIn_of_unapplied`). -/
def HupFact [GooseExts] (s s' : NState) : Prop :=
  s'.logst = s.logst ∧ s.logst.snap = none ∧ (¬ ∃ e ∈ unappliedEnts s.logst, IsConfEnt e) ∧
  uint.Z s.logst.prev.index' ≤ uint.Z s.logst.applied ∧
  uint.Z s.logst.applied ≤ uint.Z s.logst.committed ∧ uint.Z s.logst.committed + 1 < 2 ^ 64

/-- (2026-10-25, T-M M2b) and a pre-candidate that stays one keeps its log, commit and pending
snapshot (`PreKeep`: nothing of its term reached it, which would have made it a follower), and
one that a `MsgHup` made one has `hup`'s check (`HupFact`): what keeps `StepR.campaign`'s guard
from the pre-campaign to the campaign a won pre-vote runs (`PreGuard`). -/
def PreCandStep [GooseExts] (m : MessageM) (s s' : NState) : Prop :=
  (s'.role = .preCandidate → s'.term = s.term ∧
    ((s.role = .preCandidate ∧ PreKeep s s') ∨ (m.Type' = MsgHup ∧ HupFact s s'))) ∧
  SnapRoleBack s s'

macro "pc_tac" : tactic => `(tactic| (refine ⟨?_, ?_⟩; pc1_tac; srb_tac))

def TermStep [GooseExts] (m : MessageM) (s s' : NState) : Prop :=
  uint.Z s.term ≤ uint.Z s'.term ∧
  (m.Type' = MsgHup → uint.Z s'.term ≤ uint.Z s.term + 1) ∧
  (m.Type' ≠ MsgHup → m.Type' ≠ MsgPreVoteResp → m.Type' ≠ MsgTimeoutNow →
     uint.Z s'.term ≤ max (uint.Z s.term) (uint.Z m.Term')) ∧
  (m.Type' ≠ MsgApp → uint.Z s.logst.inprogress ≤ uint.Z s'.logst.inprogress) ∧
  (m.Type' = MsgTimeoutNow → uint.Z s'.term ≤ max (uint.Z s.term) (uint.Z m.Term') + 1) ∧
  PreCandStep m s s'

/-- A step that keeps the term. -/
theorem TermStep.of_term [GooseExts] {m : MessageM} {s s' : NState}
    (h : s'.term = s.term)
    (hi : m.Type' ≠ MsgApp → uint.Z s.logst.inprogress ≤ uint.Z s'.logst.inprogress)
    (hpc : PreCandStep m s s' := by pc_tac) :
    TermStep m s s' := by
  unfold TermStep; rw [h]
  exact ⟨Int.le_refl _, fun _ => by omega, fun _ _ _ => Int.le_max_left _ _, hi,
    fun _ => by have := Int.le_max_left (uint.Z s.term) (uint.Z m.Term'); omega, hpc⟩

theorem TermStep.refl [GooseExts] (m : MessageM) (s : NState) : TermStep m s s :=
  TermStep.of_term rfl (fun _ => Int.le_refl _)
    ⟨fun h => ⟨rfl, .inl ⟨h, rfl, rfl, rfl, fun h => h, Int.le_refl _⟩⟩, fun h1 h2 => ⟨h1, h2⟩⟩

/-- A step to a term between the start's and the message's, for a message other than
`MsgHup` (a step-down to `m.Term`, then a handler that keeps it). -/
theorem TermStep.of_le [GooseExts] {m : MessageM} {s s' : NState}
    (hup : m.Type' ≠ MsgHup) (h1 : uint.Z s.term ≤ uint.Z s'.term)
    (h2 : uint.Z s'.term ≤ uint.Z m.Term')
    (hi : m.Type' ≠ MsgApp → uint.Z s.logst.inprogress ≤ uint.Z s'.logst.inprogress)
    (hpc : PreCandStep m s s' := by pc_tac) :
    TermStep m s s' :=
  ⟨h1, fun h => absurd h hup, fun _ _ _ => Int.le_trans h2 (Int.le_max_right _ _), hi,
   fun _ => by have := Int.le_max_right (uint.Z s.term) (uint.Z m.Term'); omega, hpc⟩

/-- A local step's frame keeps the term and does not move `offsetInProgress` back; (2026-10-25,
T-M M2b) at a pre-candidate it keeps the log and the commit index (`PreKeep`). -/
theorem TermStep.of_local [GooseExts] {m : MessageM} {s s' : NState}
    (h : LocalFrame s s') (hk : s.role = .preCandidate → PreKeep s s') : TermStep m s s' :=
  TermStep.of_term h.1 (fun _ => h.2.1) ⟨fun hp =>
    have hr : s.role = .preCandidate := h.2.2.2.2.2.2.2.2.2.1 ▸ hp
    ⟨h.1, .inl ⟨hr, hk hr⟩⟩,
    fun h1 h2 => ⟨h.2.2.2.2.2.2.2.2.2.1 ▸ h1, h.2.2.2.1 ▸ h2⟩⟩

/-- (2026-10-25, T-M M2b) **A step keeps a pre-candidate's campaign guard** (`PreGuardF`: over a
full prefix of the log's boundary's length): a pre-candidate that stays one kept its boundary, log,
commit index and pending snapshot, and `applied` did not move back (`PreKeep`); one that a `MsgHup`
made one has `hup`'s check (`HupFact`), which is the guard on the full log (`noConfIn_of_unapplied`). -/
theorem PreGuardF.pc [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] {m : MessageM}
    {s s' : NState} (h : PreCandStep m s s') {fp : List EntryM} (hg : PreGuardF fp s) :
    PreGuardF fp s' := by
  intro hl hp
  obtain ⟨-, ⟨hr, hpr, hlog, hc, hsn, ha⟩ | ⟨-, hls, hsn, hno, h1, h2, h3⟩⟩ := h.1 hp
  · obtain ⟨hsn0, hno0⟩ := hg (by rw [← hpr]; exact hl) hr
    refine ⟨hsn hsn0, ?_⟩
    rw [hlog, hc]
    intro k e hk1 hk2 he
    have := uint_nat_eq s.logst.applied
    have := uint_nat_eq s'.logst.applied
    exact hno0 k e (by omega) hk2 he
  · rw [hls] at hl ⊢
    exact ⟨hsn, noConfIn_of_unapplied s.logst fp hl h1 h2 h3 hno⟩

/-- `PreGuardF.pc` for a `TermStep`. -/
theorem PreGuardF.step [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] {m : MessageM}
    {s s' : NState} (h : TermStep m s s') {fp : List EntryM} (hg : PreGuardF fp s) :
    PreGuardF fp s' :=
  PreGuardF.pc h.2.2.2.2.2 hg

/-- What a response does to the role and the term (2026-10-10), beyond `TermStep`: a
stale `MsgVoteResp` or `MsgAppResp` (from a term below the node's) leaves the role; a
`MsgPreVoteResp` moves the term at most to the message's, or one up from a
pre-candidate (a won pre-vote's `campaign`), and never makes the node a pre-candidate
(nor changes the term of one). `RawNode.Advance` steps the node's own responses, queued
by `Ready`: with this, stepping them all moves the term up by at most one -- once a
pre-vote is won the node is a candidate, and stays one through the rest of the queue,
whose responses are then all stale or a candidate's to ignore. -/
def RespStep [GooseExts] (m : MessageM) (s s' : NState) : Prop :=
  ((m.Type' = MsgVoteResp ∨ m.Type' = MsgAppResp) →
     uint.Z m.Term' < uint.Z s.term → s'.role = s.role) ∧
  (m.Type' = MsgPreVoteResp →
     (uint.Z s'.term ≤ max (uint.Z s.term) (uint.Z m.Term') ∨
      (s.role = .preCandidate ∧ uint.Z s'.term = uint.Z s.term + 1)) ∧
     (s'.role = .preCandidate → s.role = .preCandidate ∧ s'.term = s.term))

theorem RespStep.refl [GooseExts] (m : MessageM) (s : NState) : RespStep m s s :=
  ⟨fun _ _ => rfl, fun _ => ⟨.inl (Int.le_max_left _ _), fun h => ⟨h, rfl⟩⟩⟩

/-- Any step of a message that is none of the three responses. -/
theorem RespStep.of_type [GooseExts] {m : MessageM} {s s' : NState}
    (h1 : m.Type' ≠ MsgVoteResp) (h2 : m.Type' ≠ MsgAppResp)
    (h3 : m.Type' ≠ MsgPreVoteResp) : RespStep m s s' :=
  ⟨fun h => by rcases h with h | h <;> contradiction, fun h => absurd h h3⟩

/-- Any step of a `MsgVoteResp` or `MsgAppResp` that is not stale. -/
theorem RespStep.of_fresh [GooseExts] {m : MessageM} {s s' : NState}
    (h3 : m.Type' ≠ MsgPreVoteResp) (hge : uint.Z s.term ≤ uint.Z m.Term') :
    RespStep m s s' :=
  ⟨fun _ hlt => absurd hlt (Int.not_lt.2 hge), fun h => absurd h h3⟩

/-- (2026-10-20, D22 S-c) What a `MsgSnap`'s step leaves of the state beyond the protocol, and how
it moves the term: as `NetFrame`, but for the log's boundary and its pending snapshot, which a
restore sets (`logRestore`: the snapshot's id, and the snapshot pending), and with `applied` kept;
the term as `TermStep`'s, but for `offsetInProgress`, which a restore moves to the snapshot's index
plus one (back, when the snapshot is below the log's last index). The role is a follower's after
a snapshot of the current or a later term, and unchanged after a stale one (`PreCandStep`). What
the `RawNode` predicate needs to survive a `MsgSnap` (`RawNode.Step`). -/
def SnapStep [GooseExts] (m : MessageM) (s s' : NState) : Prop :=
  s'.logst.applying = s.logst.applying ∧
  s'.logst.unpersisted = s.logst.unpersisted ∧
  s'.logst.stored = s.logst.stored ∧
  s'.logst.storage = s.logst.storage ∧
  s'.prevote = s.prevote ∧
  s'.gh = s.gh ∧
  s'.logst.fl = s.logst.fl ∧ s'.logst.applied = s.logst.applied ∧
  uint.Z s.term ≤ uint.Z s'.term ∧ uint.Z s'.term ≤ max (uint.Z s.term) (uint.Z m.Term') ∧
  PreCandStep m s s'

/-- (D22 S-d3b, 2026-10-21) **What a `MsgApp`'s step does to the in-progress entries**: it moves
`offsetInProgress` back only by a truncation (`TruncAt`: above the commit index, at an entry of the
message's batch the log did not have), and only at the message's term. With the leader's log the
message carries (`isMessage`), this is what the `RawNode` keeps of a batch a `Ready` handed out
that a `MsgApp` cut (`ackLostW`, `InvRawnode.lean`), for a later restore's Log Matching. -/
def AppTrunc [GooseExts] (m : MessageM) (ents : List EntryM) (s s' : NState) : Prop :=
  uint.Z s'.logst.inprogress < uint.Z s.logst.inprogress →
  s'.term = m.Term' ∧ TruncAt s.logst ents s'.logst.inprogress

/-- A step that keeps `offsetInProgress`. -/
theorem AppTrunc.of_ip [GooseExts] {m : MessageM} {ents : List EntryM} {s s' : NState}
    (h : s'.logst.inprogress = s.logst.inprogress) : AppTrunc m ents s s' :=
  fun hl => absurd hl (by rw [h]; exact Int.lt_irrefl _)

/-- A dropped snapshot's step. -/
theorem SnapStep.refl [GooseExts] (m : MessageM) (s : NState) : SnapStep m s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Int.le_refl _, Int.le_max_left _ _,
    ⟨fun h => ⟨rfl, .inl ⟨h, rfl, rfl, rfl, fun h => h, Int.le_refl _⟩⟩, fun h1 h2 => ⟨h1, h2⟩⟩⟩

/-- (D22 S-d3b, 2026-10-21) **What a `MsgSnap`'s step does to the log**, for its snapshot `sv`: the
log's boundary, entries, pending snapshot and `offsetInProgress` kept (a stale snapshot, or one the
log already has: the commit index fast-forwarded), or `restore`'s third exit -- at the message's
term, past the commit index, of a snapshot whose last entry the log did not have (`!matchTerm`),
the log now the snapshot alone. The `RawNode` needs the restore's facts for the acknowledgement of
a `Ready` the restore came between (`ackBaseW`, `InvRawnode.lean`). -/
def SnapLogStep [GooseExts] (sv : SnapshotM) (m : MessageM) (s s' : NState) : Prop :=
  (s'.logst.prev = s.logst.prev ∧ s'.logst.snap = s.logst.snap ∧
   s'.logst.sents ++ s'.logst.uents = s.logst.sents ++ s.logst.uents ∧
   s'.logst.inprogress = s.logst.inprogress) ∨
  (s'.term = m.Term' ∧ s'.logst.prev = snapId sv ∧ s'.logst.snap = some (snapId sv) ∧
   s'.logst.sents ++ s'.logst.uents = [] ∧
   uint.Z s.logst.committed < uint.Z sv.Metadata'.Index' ∧
   ¬ PlogMatches s.logst.prev (s.logst.sents ++ s.logst.uents) (snapId sv))

theorem SnapLogStep.refl [GooseExts] (sv : SnapshotM) (m : MessageM) (s : NState) :
    SnapLogStep sv m s s :=
  .inl ⟨rfl, rfl, rfl, rfl⟩

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
-- `hlc := HasLC.hasLC`, so that the heap's invariants are an `InvGS GF` (see the
-- Lean notes)
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The top-level dispatch, and **one spec like every other function**. The
per-message-type branches are proof structure, not specification: since 2026-09-17
they live in `proof_raft__Step_MsgHup.v`, `_MsgVote.v`, `_MsgVoteResp.v` and
(2026-10-02) `_MsgProp.v` (and below those, `_MsgVote_gt.v`, `_MsgVote_le.v`,
`_MsgVote_lt.v`, `_MsgVote_eq_novote.v`, `_MsgVote_eq_voted.v`), each a functor over
`STEP_POSTULATES` with no `Module Type` and no `Parameter`, so that `make -j` checks
them in parallel. Only `proof_raft__Step.v` and the combining files may `Require` one.
(An earlier version of this note said `Step` "is the one function with more than one
spec"; that was written before the first cut's three per-message-type `Module Type`s
were removed on 2026-09-14, and it is no longer true of anything here.)

This is **the only spec in this development that mentions ghost state**. Every
function below it is specified against `ownRaftPhys` alone, saying which state the
struct ends up refining and how the outbox grew; `Step` assembles those pure facts into
one `Step` witness and takes one `ownRaftGhost_step`. A caller that needs to know a
pending outgoing message is protocol-legal gets that from `ownRaftGhost_outbox`, not
from `ownRaftPhys`. -/
abbrev raft.Step.spec : Prop :=
  ∀ (c : CfgM)
    -- (2026-10-14, stage B7) the mode of the ghost state: static (`ownRaftGhost`, at a
    -- configuration with the ghost state's voters) or dynamic (`ownRaftGhostR`, the node's
    -- reconfiguration state over the struct's configuration); see `StepGhostMode.lean`
    (md : GMode)
    (γ : RaftNames) (r : Loc) (id : w64) (s : NState)
    -- (stage R4) the message's pointer; its scalars `m`, entries `ents`, context `ctx`,
    -- snapshot `sn` and responses `rs`
    (ml : Loc) (m : MessageM)
    -- The message's `Entries` (`[]` for a message without entries), bound here rather
    -- than in `"Hm"` since 2026-10-06. (Until 2026-10-10 also, for a `MsgProp`, the
    -- client's result predicate for each entry: a proposal's atomic update is now
    -- deposited before the proposal reaches `Step` (`prop_deposit`), and its entries'
    -- `isMessage` says so (`entData`).)
    (ents : List EntryM)
    -- (2026-10-12) the list the message's `Context` holds, which the abstract message
    -- carries (a heartbeat's response echoes it; a forwarded proposal keeps it)
    (ctx : List w8) (sn : Option SnapshotM) (rs : List Loc),
  StepMsg m →
  -- (Until 2026-10-14, stage B8, a premise `m.Type' = MsgSnap → id ∈ γ.reCfg`: the node one of
  -- the ghost state's voters, which a snapshot's `restore` needs. It is now one of the
  -- snapshot's ids, in `"Hsnap"`.)
  -- A `MsgHup` is local (`Term = 0`) and may start an election, which increments the
  -- term; `send` panics if that wraps to zero.
  (m.Type' = MsgHup →
     m.Term' = W64 0 ∧
     uint.Z s.term + 1 < 2 ^ 64 ∧
     -- (2026-10-17) with pre-vote on a `MsgHup` pre-campaigns: its `MsgPreVote`s are of the next
     -- term, which the ceiling (`NGhost.tc`) must cover; the `RawNode` raises it first
     (s.prevote = true → uint.Z s.term + 1 ≤ uint.Z s.gh.tc) ∧
     -- (D19i part 1) the floor at most `applied` (`hup`'s)
     uint.Z s.logst.fl ≤ uint.Z s.logst.applied) →
  (m.Type' = MsgVote →
     m.To' = id ∧ m.Term' ≠ W64 0 ∧
     m.From' ≠ W64 0) →
  (m.Type' = MsgVoteResp →
     m.To' = id ∧ m.Term' ≠ W64 0) →
  -- Pre-vote (2026-10-04), by what the transport and the peers guarantee, like
  -- `MsgVote`; Go checks none of it. Two more:
  -- - a `MsgPreVote` of a higher term is answered at the node's own term when the
  --   candidate's log is behind (`Term: r.Term, Reject: true`; the term is not raised
  --   for a pre-vote), and `send` panics on a vote message with `Term = 0`. So a node
  --   at term `0` must find every pre-vote candidate up to date -- true of a node
  --   whose log holds nothing past term `0`, i.e. of every node etcd builds (a fresh
  --   node has an empty log; `Bootstrap` and `RestartNode` start at a term of at
  --   least the log's), but not implied by `ownRaftPhys`, which admits a persisted
  --   log ahead of the persisted term;
  -- - a `MsgPreVoteResp` at a pre-candidate may win, which runs the real `campaign`
  --   and increments the term: it must not wrap (as for `MsgHup`). Only at a
  --   pre-candidate (2026-10-10: `RawNode.Advance` may step its own pre-vote response
  --   after a won pre-vote raised the term, at a candidate, which ignores it);
  -- - a `MsgPreVote`'s term within the node's term ceiling (`NGhost.tc`; 2026-10-17, until
  --   then it reached only a node with pre-vote on, and `RawNode.Step` took none): a granted
  --   pre-vote answers at the request's term (`OutTermOk`).
  (m.Type' = MsgPreVote →
     m.To' = id ∧ m.Term' ≠ W64 0 ∧
     m.From' ≠ W64 0 ∧ m.From' ≠ id ∧
     (s.term = W64 0 →
      plogUpToDate s.logst.prev (s.logst.sents ++ s.logst.uents)
        (entryID.mk m.LogTerm' m.Index') = true) ∧
     -- (2026-10-17) a grant answers at the requested term, which the ceiling (`NGhost.tc`)
     -- must cover when it is past the node's; the `RawNode` raises it first
     (uint.Z m.Term' ≤ uint.Z s.term ∨ uint.Z m.Term' ≤ uint.Z s.gh.tc)) →
  (m.Type' = MsgPreVoteResp →
     m.To' = id ∧ m.Term' ≠ W64 0 ∧
     m.From' ≠ W64 0 ∧
     (s.role = .preCandidate → uint.Z s.term + 1 < 2 ^ 64)) →
  -- The replication types, by what the transport and the peers guarantee (Go checks
  -- none of it). A leader's `MsgApp`/`MsgHeartbeat`, and a `MsgHeartbeatResp`, come
  -- from another node: `send` never queues them to oneself. An accepting
  -- `MsgAppResp` may be the node's own (`appendEntry`'s self-acknowledgement); a
  -- rejecting one is not.
  (m.Type' = MsgApp →
     m.To' = id ∧ m.Term' ≠ W64 0 ∧
     m.From' ≠ W64 0 ∧ m.From' ≠ id) →
  (m.Type' = MsgHeartbeat →
     m.To' = id ∧ m.Term' ≠ W64 0 ∧
     m.From' ≠ W64 0 ∧ m.From' ≠ id) →
  (m.Type' = MsgAppResp →
     m.To' = id ∧ m.Term' ≠ W64 0 ∧
     m.From' ≠ W64 0 ∧
     (m.Reject' = true → m.From' ≠ id)) →
  (m.Type' = MsgHeartbeatResp →
     m.To' = id ∧ m.Term' ≠ W64 0 ∧
     m.From' ≠ W64 0 ∧ m.From' ≠ id) →
  -- A leader's `MsgSnap`, likewise (2026-10-02).
  (m.Type' = MsgSnap →
     m.To' = id ∧ m.Term' ≠ W64 0 ∧
     m.From' ≠ W64 0 ∧ m.From' ≠ id) →
  -- `MsgBeat` and `MsgProp` are local (`Term = 0`); a proposal is not yet stamped
  -- with a sender (`From = 0`), or is stamped with the node's own id
  -- (`RawNode.Propose` sets `From: r.id`; since 2026-10-06). The proposal's batch is
  -- constrained in `Hm` below, where its list is named.
  -- (2026-10-17, `CheckQuorum` on) so is the quorum check `tickHeartbeat` steps
  (m.Type' = MsgBeat ∨ m.Type' = MsgCheckQuorum → m.Term' = W64 0) →
  (m.Type' = MsgProp →
     m.Term' = W64 0 ∧
     (m.From' = W64 0 ∨ m.From' = id)) →
  -- The two local acknowledgements `RawNode.Advance` steps (2026-10-05), as
  -- `acceptReady` builds them (`InvRawnode.lean`, `appendAckMsg`, `applyAckMsg`). A
  -- `MsgStorageAppendResp` (until D22 S-d2 carrying no snapshot) is not from a later term (it would make the node
  -- step down to a term no message brought), and -- when its `stableTo` runs (`Term`
  -- `0` or current, a nonzero `Index`) -- acknowledges only persisted entries
  -- (`StableOk`: Go compares only the term at `Index`). A `MsgStorageApplyResp` is
  -- local (`Term = 0`); its entries' last index is committed (the bound is in `"Hm"`,
  -- where the list is named).
  -- (D22 S-d2, 2026-10-21) It may carry a snapshot (until then `sn = none`), the one the
  -- storage is at if it is the pending one (`sat`; the application's receipt absorbed before
  -- the step), at or below the log's boundary (the pending one, or older after a second restore),
  -- in the static mode (the dynamic mode takes no snapshot), with `appliedTo`'s auto-leave
  -- premise; the `StableOk` is of the log in the window the arm opens (`ackLog`).
  (m.Type' = MsgStorageAppendResp →
     (∀ sv, sn = some sv →
        snapHit s.logst.snap sv.Metadata'.Index' = s.logst.sat ∧
        uint.Z sv.Metadata'.Index' ≤ uint.Z s.logst.prev.index' ∧
        md.isDyn = false ∧
        -- (2026-10-28, stage U0; until then `appliedTo`'s auto-leave premise, `c.autoLeave = true →
        -- s.role ≠ .leader`) `appliedSnap`'s rebuild: a follower, the snapshot as `SnapAckOk`
        s.role = .follower ∧ SnapAckOk γ id sv ∧
        -- (D22 S-d4 item 3) with a snapshot pending and the storage back, the storage holds the
        -- log up to the acknowledged snapshot (`LogState.sxt`; `appliedSnap` moves `applying` there)
        (s.logst.snap ≠ none → s.logst.lent = false →
          uint.Z sv.Metadata'.Index' ≤ uint.Z s.logst.sxt) ∧
        (∀ k, s.gh.snp = some k → uint.Z k.sid.index' ≤ uint.Z sv.Metadata'.Index')) ∧
     uint.Z m.Term' ≤ uint.Z s.term ∧
     (m.Term' = W64 0 ∨ m.Term' = s.term →
      m.Index' ≠ W64 0 →
      StableOk (ackLog s.logst sn) (entryID.mk m.LogTerm' m.Index')) ∧
     -- (2026-10-10) `stableTo` may hand out every unstable entry still to come
     -- (`NGhost.unst`): `RawNode.Advance` steps it only after `acceptReady` reset the flag
     s.gh.unst = false) →
  (m.Type' = MsgStorageApplyResp → m.Term' = W64 0) →
  -- Read-index (2026-10-13): a request is unstamped (`Term = 0`; a local one from
  -- `ReadIndex`, a forwarded one from a follower); a response is a leader's, from another
  -- node. (Until 2026-10-14 also not in a single-voter configuration, `IsSingleton`'s
  -- immediate answer: in scope since the pinned raft has the fix of
  -- `issues/raft-readindex-singleton-stale.md`.)
  (m.Type' = MsgReadIndex → m.Term' = W64 0) →
  -- (2026-10-14, stage B7) `appliedTo`'s auto-leave proposal is out of scope: no `AutoLeave`
  -- at a leader (`raft.appliedTo.spec`)
  (m.Type' = MsgStorageApplyResp → c.autoLeave = true → s.role ≠ .leader) →
  (m.Type' = MsgReadIndexResp →
     m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0 ∧ m.From' ≠ id) →
  -- (2026-10-13) the local reports, `ForgetLeader` and leader transfer (`RestMsgOk`)
  RestMsgOk s m ents ctx →
  -- `r.step` agrees with the role (until 2026-10-14 `NStateRel s ps`, with the protocol
  -- state `ps` the ghost state was about: now `toPState s`, in `ownStepGhost`)
  NStateWf s →
  -- (2026-10-14, stage B7) the dynamic mode's premises (`GMode.Pre`): no `MsgSnap` (a
  -- snapshot restore at a dynamic configuration is stage B8), a pre-candidate only with its
  -- campaign guard (`PreGuardF`; 2026-10-25, T-M M2b: until then none, pre-vote off at the
  -- `RawNode` API), A1 at a `MsgStorageApplyResp` (no conf entry between the
  -- configuration index and the acknowledged index: `ApplyConfChange` before `Advance`), and a
  -- log short enough for a dropped proposal's `pendingConfIndex`; none in the static mode
  md.Pre m ents s →
  -- (2026-10-19, D21 M3) no snapshot in the no-snapshot mode (`NGhost.ns`; `RawNode.Step` takes
  -- none)
  (m.Type' = MsgSnap → s.gh.ns = false) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      "Hghost" ∷ ownStepGhost γ md c id s ∗
      -- The message's `Entries` slice, holding `ents` (`[]` for a message without
      -- entries, `Entries = nil`):
      -- - a proposal is a local message whose batch the caller owns outright --
      --   `appendEntry` writes `Term`/`Index` into the entries -- while every network
      --   message's entries are read-only;
      -- - the slice's capacity, owned: `raftLog.maybeAppend` can adopt the caller's
      --   slice (`unstable.truncateAndAppend`'s replace arm), so a received `MsgApp`
      --   needs it;
      -- - a proposal's batch is non-empty (`stepLeader`'s `Panicf`) and short enough for
      --   `appendEntry`'s indices not to wrap, and (2026-10-13, reconfiguration stage D;
      --   until then `EntryNormal` only) its conf-change entries' bytes decode (`ccEntsOk`:
      --   `stepLeader` `Unmarshal`s them, panicking on an error);
      -- - what the message carries as a protocol message: its abstraction (`absMsg`,
      --   which needs the entries) was legitimately sent -- for every type but
      --   `MsgSnap`, whose abstraction is `absSnap` (`"Hsnap"` below).
      -- (stage R4) the message, taken for good (`msgIn`: the struct, the `Entries` capacity
      -- and the snapshot owned; the entry pointers owned for a `MsgProp`, read-only
      -- otherwise; the `Context` holding `ctx`)
      "Hm" ∷ (
         "Hmsg_in" ∷ msgIn ml (if m.Type' = MsgProp then DFrac.own 1 else DFrac.discard)
                       ⟨m, ents, sn, ctx, rs⟩ ∗
         -- a proposal's conf-change entries' bytes, which decode
         -- (2026-10-19, D21 M6) and its entries' tickets (`entTk`), which the leader consumes
         "Hents" ∷ (if m.Type' = MsgProp then
                      iprop((∃ cs, ccEntsOk ents cs) ∗ [∗list] e ∈ ents, entTk γ e) else emp) ∗
         "%Hprop" ∷ ⌜m.Type' = MsgProp →
                      ents ≠ [] ∧
                      (ents.length : Int) < 2^61⌝ ∗
         -- (2026-10-22, D38a) a message a follower forwards to the leader has no responses
         -- (`send`'s premise; raft sets them only on its local storage messages)
         "%Hnors" ∷ ⌜m.Type' = MsgProp ∨ m.Type' = MsgReadIndex ∨ m.Type' = MsgTransferLeader →
                      rs = []⌝ ∗
         -- (D19i part 1) and at most `applying` (`RawNode.Advance` acknowledges entries
         -- `Ready` handed out; `appliedTo` then leaves `applying`)
         "%Happly" ∷ ⌜m.Type' = MsgStorageApplyResp →
                       ∀ e, ents.getLast? = some e →
                       uint.Z e.Index' ≤ uint.Z s.logst.committed ∧
                       uint.Z e.Index' ≤ uint.Z s.logst.applying⌝ ∗
         "#Hmsg" ∷ □ (∀ ty, ⌜mtypeOf m.Type' = some ty⌝ -∗
                            ⌜ty ≠ .snap⌝ -∗
                            isMessage γ (absMsg ty m ents ctx))) ∗
      -- the `Context`. (Until 2026-10-13 not the leader-transfer marker -- a transfer's
      -- vote request is now an ordinary one, whose `force` only bypasses the lease check
      -- (2026-10-17, `checkQuorum` on) -- and empty on a heartbeat response; a read-index position is now what
      -- `isMessage` says it is.)
      -- (2026-10-13) a read-index request carries a read credit (`rdOwn`)
      "Hcred" ∷ rdCred γ (if m.Type' = MsgReadIndex then 1 else 0) ∗
      -- (2026-10-14, stage R) a later credit, for the ghost step: the commit invariant's
      -- registry half is opened around it, its persistent updates fired at every commit
      "Hlc" ∷ £ 1 ∗
      -- A `MsgSnap`'s snapshot (2026-10-02; any `ConfState` since 2026-10-14, stage B8): what
      -- `m.Snapshot` points to, read-only, and the four lists `scfg` its `ConfState`'s
      -- slices hold, read-only (`ownCSL`); well formed (`SnapScope`, `Spec/raft__restore.lean`:
      -- `CSWf`, no repeats, `AutoLeave` off when not joint, the index below `2^61` -- a pending
      -- snapshot becomes the `Storage`'s boundary, which `isStorage`'s `Hbounded` bounds the
      -- same way) (since D22 S-b, D22j, naming the node or not: `restore`'s `!found` exit refuses
      -- it, `Step.snapStale`; until then a premise `CSLists.Has`); what the mode asks of it
      -- (`GMode.SnapOk`: statically the ghost state's voters, not joint; dynamically A3, the
      -- `ConfState` the fold of the snapshot's prefix); and the abstraction `absSnap`
      -- (`Defs.lean`) -- the snapshot's metadata, not `m`'s own `Index`/`LogTerm` -- was
      -- legitimately sent. Transport/client assumptions like the rest. (Since D22 S-b′4,
      -- 2026-10-20, the scope and the static mode's need are the message certificate's, under
      -- the lists' naming the node, `SnapScopeIf`/`GMode.SnapOkIf`: only the index bound and,
      -- dynamically, `GMode.SnapOk` (`GMode.SnapDyn`) are left.)
      -- (stage R4) the snapshot the message holds (`sn = some sv`, owned in `"Hm"`) and the
      -- lists of its `ConfState` (until the retarget the read-only slices, `ownCSL`)
      "#Hsnap" ∷ □ (⌜m.Type' = MsgSnap⌝ -∗
         ∃ (sv : SnapshotM) (scfg : CSLists),
           -- (D22 S-b′4, 2026-10-20) the index bound only: the lists' scope and, statically, what
           -- the mode asks come from the message's certificate (under its naming the node)
           ⌜sn = some sv ∧ scfg = sv.Metadata'.ConfState'.lists ∧
             uint.Z sv.Metadata'.Index' < 2^61⌝ ∗
           md.SnapDyn γ sv scfg ∗
           -- (D22 S-b′3, 2026-10-20) certified (`isMessageC`): its snapshot's configuration
           -- certificate, which the step registers in the storage (`certLink`) before the restore
           isMessageC γ (absSnap m sv scfg) ∗
           -- (D22 S-r, 2026-10-21) and its data certificate, registered with it
           snapDataOk γ sv.Metadata'.Index' sv.Data') }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
  {{ (err : GoInterface) (s' : NState) (c' : CfgM) (md' : GMode), RET #err;
      "Hphys" ∷ ownRaftPhysCV c' c'.voters r id s' ∗
      "Hghost" ∷ ownStepGhost γ md' c' id s' ∗
      "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
      -- the step in the mode's model: `StepC c` statically, `StepR` dynamically
      -- (2026-10-14, stage B7 part 2) and in the dynamic mode the configuration index moves only
      -- by a `MsgStorageApplyResp` (`CidxMove`)
      "%Hrefines" ∷ ⌜md.StepOut c id m s s' md'⌝ ∗
      -- the configuration afterwards: `c`, but the snapshot's after its acknowledgement (2026-10-28,
      -- stage U0; until then after a `MsgSnap` that restored it)
      "%Hcfg'" ∷ ⌜(m.Type' = MsgStorageAppendResp → sn = none) → c' = c⌝ ∗
      -- for the local messages `RawNode` steps, what is kept of the physical state
      -- (2026-10-09)
      -- (D22 S-d2) but for a snapshot's acknowledgement, which moves the log as `ackSnapLog` says
      -- and nothing else
      "%Hlocal" ∷ ⌜((m.Type' = MsgStorageAppendResp → sn = none) → LocalStepOk m ents s s') ∧
                   (m.Type' = MsgStorageAppendResp → ∀ sv, sn = some sv →
                      -- (U0) at the snapshot's configuration, the tracker rebuilt
                      c' = snapCfg sv sv.Metadata'.ConfState'.lists ∧
                      ∃ (prs : GMap w64 Loc) (pvs : GMap w64 Progress) (il : Bool),
                        s' = { s with logst := ackSnapLog s.logst m s.term sv, progress := prs,
                                      prvals := pvs, isLearner := il })⌝ ∗
      -- for every other message but a snapshot (and its acknowledgement), what is kept of the
      -- log (2026-10-09)
      "%Hframe" ∷ ⌜m.Type' ≠ MsgSnap → m.Type' ≠ MsgStorageApplyResp →
                   (m.Type' = MsgStorageAppendResp → sn = none) → NetFrame s s'⌝ ∗
      -- and how the term moves (2026-10-09)
      "%Hterm" ∷ ⌜m.Type' ≠ MsgSnap → TermStep m s s'⌝ ∗
      -- and what a response does to the role and the term (2026-10-10)
      "%Hresp" ∷ ⌜RespStep m s s'⌝ ∗
      -- (2026-10-20, D22 S-c) for a snapshot, what is kept of the state and how the term moves
      -- (`SnapStep`) (until stage U0 also the configuration afterwards, `SnapCfgOut`)
      "%Hsnapfr" ∷ ⌜m.Type' = MsgSnap → SnapStep m s s' ∧
                     -- (D22 S-d3b) and what it did to the log (`SnapLogStep`)
                     ∀ sv, sn = some sv → SnapLogStep sv m s s'⌝ ∗
      -- (D22 S-d3b, 2026-10-21) a `MsgApp`'s truncation's mark (`AppTrunc`)
      "%Htrunc" ∷ ⌜m.Type' = MsgApp → AppTrunc m ents s s'⌝ ∗
      -- only a proposal can be dropped, with `ErrProposalDropped`
      "Herr" ∷ (⌜err = interface.nil⌝ ∨
                (⌜m.Type' = MsgProp⌝ ∗
                 globalAddr ErrProposalDropped ↦□ err)) }}

end spec

end EtcdGrove
end Perennial
