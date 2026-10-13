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
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys
-- `StableOk`, for `MsgStorageAppendResp` (2026-10-05)
public import Proof.go_etcd_io.raft.v3.InvReadylog
public import Proof.go_etcd_io.raft.v3.InvConfChangeMsg
-- `SnapScope`, for `MsgSnap`
public import Spec.go_etcd_io.raft.v3.raft__restore
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
2026-10-05). -/
def stepMsgTypes : List w32 :=
  [MsgHup, MsgVote, MsgVoteResp, MsgApp, MsgAppResp, MsgHeartbeat,
   MsgHeartbeatResp, MsgBeat, MsgProp, MsgSnap, MsgPreVote, MsgPreVoteResp,
   MsgStorageAppendResp, MsgStorageApplyResp, MsgReadIndex, MsgReadIndexResp,
   MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTransferLeader, MsgTimeoutNow]

/-- (2026-10-13) The premises of the types `Step` was extended to last: the local reports
(`ReportUnreachable`, `ReportSnapshot`) and `ForgetLeader` are unstamped (`Term = 0`);
a `MsgTimeoutNow` makes a follower campaign, at the message's term if it is later, so
neither term wraps; and a leader-transfer request stamped with a term (forwarded by a
follower to the leader it knew, `To: r.lead`) reaches a node that, at that term, is no
follower with a leader -- the leader it was sent to stays leader for the term (with
`checkQuorum` off a leader steps down only to a later term) -- since a follower would
forward it again and `send` panics on a stamped `MsgTransferLeader`; and it carries no
entries and no context (`RawNode.TransferLeader` builds it so, and forwarding keeps it).
These are transport premises, like the others: no message fact carries them
(`MsgTransferLeader` and `MsgTimeoutNow` are outside the model, `mtypeOf` is `none`). -/
def RestMsgOk [FfiSyntax] (s : NState) (m : raftpb.Message) : Prop :=
  ((m.Type' = MsgForgetLeader ∨ m.Type' = MsgUnreachable ∨ m.Type' = MsgSnapStatus) →
     m.Term' = W64 0) ∧
  (m.Type' = MsgTimeoutNow → uint.Z s.term + 1 < 2 ^ 64 ∧ uint.Z m.Term' + 1 < 2 ^ 64) ∧
  (m.Type' = MsgTransferLeader →
     m.Entries' = slice.nil ∧ m.Context' = slice.nil ∧
     (m.Term' ≠ W64 0 → m.Term' = s.term → s.role = .follower → s.lead = W64 0))

/-- `RestMsgOk` of a message of none of those types. -/
theorem RestMsgOk.of_ne [FfiSyntax] {s : NState} {m : raftpb.Message}
    (h : m.Type' ≠ MsgForgetLeader ∧ m.Type' ≠ MsgUnreachable ∧ m.Type' ≠ MsgSnapStatus ∧
      m.Type' ≠ MsgTimeoutNow ∧ m.Type' ≠ MsgTransferLeader) : RestMsgOk s m :=
  ⟨fun h' => by rcases h' with h' | h' | h' <;> simp_all,
   fun h' => absurd h' h.2.2.2.1, fun h' => absurd h' h.2.2.2.2⟩

def StepMsg [FfiSyntax] (m : raftpb.Message) : Prop :=
  m.Type' ∈ stepMsgTypes

/-- What a `Step` of one of the messages `RawNode` steps itself leaves of the node's
physical state beyond the protocol (2026-10-09): the term, the entries a `Ready` handed
out that the application has not appended yet (`unpersisted`), the pending snapshot,
and `offsetInProgress`, which does not move back; and (2026-10-10) the log's boundary
and what the storage holds (`prev`, the ghost `stored`), which the `RawNode` predicate
keeps the records of for the acknowledgement `Advance` steps (`InvRawnode.lean`); and
the storage the log reads (`LogState.storage`, constant), which the `RawNode` predicate
names to its client (`RNState.storage`); and (2026-10-10) `r.preVote`. -/
def LocalFrame [FfiSyntax] (s s' : NState) : Prop :=
  s'.term = s.term ∧
  uint.Z s.logst.inprogress ≤ uint.Z s'.logst.inprogress ∧
  s'.logst.unpersisted = s.logst.unpersisted ∧
  s'.logst.snap = s.logst.snap ∧
  s'.logst.prev = s.logst.prev ∧
  s'.logst.stored = s.logst.stored ∧
  s'.logst.storage = s.logst.storage ∧
  s'.prevote = s.prevote ∧
  s'.gh = s.gh

/-- `Step`'s postcondition for the three local messages `RawNode` steps -- a proposal
(`Propose`) and the two storage acknowledgements (`Advance`): `LocalFrame`, and
`applying` is unchanged -- a `MsgStorageApplyResp` moves it (`appliedTo`) only past
entries not yet handed out, so not when its last entry is at or below it. This is what
lets the `RawNode` predicate (`InvRawnode.lean`) keep its client-facing facts on the log
(the committed entries handed out so far, the unpersisted ones) across a `Step`.
Nothing is said for any other message type. -/
def LocalStepOk [FfiSyntax] (m : raftpb.Message) (ents : List raftpb.Entry)
    (s s' : NState) : Prop :=
  (m.Type' = MsgProp ∨ m.Type' = MsgStorageAppendResp ∨ m.Type' = MsgStorageApplyResp) →
  LocalFrame s s' ∧
  ((m.Type' = MsgStorageApplyResp →
      ∀ e, ents.getLast? = some e → uint.Z e.Index' ≤ uint.Z s.logst.applying) →
   s'.logst.applying = s.logst.applying)

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
never written after `newRaft` (the `RawNode` predicate keeps pre-vote off, its scope). -/
def NetFrame [FfiSyntax] (s s' : NState) : Prop :=
  s'.logst.applying = s.logst.applying ∧
  s'.logst.snap = s.logst.snap ∧
  s'.logst.unpersisted = s.logst.unpersisted ∧
  s'.logst.prev = s.logst.prev ∧
  s'.logst.stored = s.logst.stored ∧
  s'.logst.storage = s.logst.storage ∧
  s'.prevote = s.prevote ∧
  s'.gh = s.gh

theorem NetFrame.refl [FfiSyntax] (s : NState) : NetFrame s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem NetFrame.trans [FfiSyntax] {s1 s2 s3 : NState} (h1 : NetFrame s1 s2)
    (h2 : NetFrame s2 s3) : NetFrame s1 s3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1,
   h2.2.2.2.2.1.trans h1.2.2.2.2.1, h2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.1, h2.2.2.2.2.2.2.2.trans h1.2.2.2.2.2.2.2⟩

/-- Two states with the same log state and pre-vote setting. -/
theorem NetFrame.of_logst [FfiSyntax] {s s' : NState} (h : s'.logst = s.logst)
    (hpv : s'.prevote = s.prevote := by rfl) (hg : s'.gh = s.gh := by rfl) :
    NetFrame s s' := by
  unfold NetFrame; rw [h, hpv, hg]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- How a `Step` moves the term (2026-10-09): never back; by a local `MsgHup` at most one
up (a campaign); by any other message (but a `MsgPreVoteResp` or (2026-10-13) a
`MsgTimeoutNow`, which may also campaign) at most to the message's term. And
`offsetInProgress` does not move back but by a `MsgApp`, whose append may truncate the
in-progress entries. And (2026-10-13, for `node.go`'s term budget) a `MsgTimeoutNow` at most
one past the larger of the node's and the message's term: a step-down to the message's
term, then a campaign. -/
def TermStep [FfiSyntax] (m : raftpb.Message) (s s' : NState) : Prop :=
  uint.Z s.term ≤ uint.Z s'.term ∧
  (m.Type' = MsgHup → uint.Z s'.term ≤ uint.Z s.term + 1) ∧
  (m.Type' ≠ MsgHup → m.Type' ≠ MsgPreVoteResp → m.Type' ≠ MsgTimeoutNow →
     uint.Z s'.term ≤ max (uint.Z s.term) (uint.Z m.Term')) ∧
  (m.Type' ≠ MsgApp → uint.Z s.logst.inprogress ≤ uint.Z s'.logst.inprogress) ∧
  (m.Type' = MsgTimeoutNow → uint.Z s'.term ≤ max (uint.Z s.term) (uint.Z m.Term') + 1)

/-- A step that keeps the term. -/
theorem TermStep.of_term [FfiSyntax] {m : raftpb.Message} {s s' : NState}
    (h : s'.term = s.term)
    (hi : m.Type' ≠ MsgApp → uint.Z s.logst.inprogress ≤ uint.Z s'.logst.inprogress) :
    TermStep m s s' := by
  unfold TermStep; rw [h]
  exact ⟨Int.le_refl _, fun _ => by omega, fun _ _ _ => Int.le_max_left _ _, hi,
    fun _ => by have := Int.le_max_left (uint.Z s.term) (uint.Z m.Term'); omega⟩

theorem TermStep.refl [FfiSyntax] (m : raftpb.Message) (s : NState) : TermStep m s s :=
  TermStep.of_term rfl (fun _ => Int.le_refl _)

/-- A step to a term between the start's and the message's, for a message other than
`MsgHup` (a step-down to `m.Term`, then a handler that keeps it). -/
theorem TermStep.of_le [FfiSyntax] {m : raftpb.Message} {s s' : NState}
    (hup : m.Type' ≠ MsgHup) (h1 : uint.Z s.term ≤ uint.Z s'.term)
    (h2 : uint.Z s'.term ≤ uint.Z m.Term')
    (hi : m.Type' ≠ MsgApp → uint.Z s.logst.inprogress ≤ uint.Z s'.logst.inprogress) :
    TermStep m s s' :=
  ⟨h1, fun h => absurd h hup, fun _ _ _ => Int.le_trans h2 (Int.le_max_right _ _), hi,
   fun _ => by have := Int.le_max_right (uint.Z s.term) (uint.Z m.Term'); omega⟩

/-- A local step's frame keeps the term and does not move `offsetInProgress` back. -/
theorem TermStep.of_local [FfiSyntax] {m : raftpb.Message} {s s' : NState}
    (h : LocalFrame s s') : TermStep m s s' :=
  TermStep.of_term h.1 (fun _ => h.2.1)

/-- What a response does to the role and the term (2026-10-10), beyond `TermStep`: a
stale `MsgVoteResp` or `MsgAppResp` (from a term below the node's) leaves the role; a
`MsgPreVoteResp` moves the term at most to the message's, or one up from a
pre-candidate (a won pre-vote's `campaign`), and never makes the node a pre-candidate
(nor changes the term of one). `RawNode.Advance` steps the node's own responses, queued
by `Ready`: with this, stepping them all moves the term up by at most one -- once a
pre-vote is won the node is a candidate, and stays one through the rest of the queue,
whose responses are then all stale or a candidate's to ignore. -/
def RespStep [FfiSyntax] (m : raftpb.Message) (s s' : NState) : Prop :=
  ((m.Type' = MsgVoteResp ∨ m.Type' = MsgAppResp) →
     uint.Z m.Term' < uint.Z s.term → s'.role = s.role) ∧
  (m.Type' = MsgPreVoteResp →
     (uint.Z s'.term ≤ max (uint.Z s.term) (uint.Z m.Term') ∨
      (s.role = .preCandidate ∧ uint.Z s'.term = uint.Z s.term + 1)) ∧
     (s'.role = .preCandidate → s.role = .preCandidate ∧ s'.term = s.term))

theorem RespStep.refl [FfiSyntax] (m : raftpb.Message) (s : NState) : RespStep m s s :=
  ⟨fun _ _ => rfl, fun _ => ⟨.inl (Int.le_max_left _ _), fun h => ⟨h, rfl⟩⟩⟩

/-- Any step of a message that is none of the three responses. -/
theorem RespStep.of_type [FfiSyntax] {m : raftpb.Message} {s s' : NState}
    (h1 : m.Type' ≠ MsgVoteResp) (h2 : m.Type' ≠ MsgAppResp)
    (h3 : m.Type' ≠ MsgPreVoteResp) : RespStep m s s' :=
  ⟨fun h => by rcases h with h | h <;> contradiction, fun h => absurd h h3⟩

/-- Any step of a `MsgVoteResp` or `MsgAppResp` that is not stale. -/
theorem RespStep.of_fresh [FfiSyntax] {m : raftpb.Message} {s s' : NState}
    (h3 : m.Type' ≠ MsgPreVoteResp) (hge : uint.Z s.term ≤ uint.Z m.Term') :
    RespStep m s s' :=
  ⟨fun _ hlt => absurd hlt (Int.not_lt.2 hge), fun h => absurd h h3⟩

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
  ∀ (cfg : GSet w64)
    (γ : RaftNames) (r : Loc) (id : w64) (s : NState) (ps : PState)
    (m : raftpb.Message)
    -- The message's `Entries` (`[]` for a message without entries), bound here rather
    -- than in `"Hm"` since 2026-10-06. (Until 2026-10-10 also, for a `MsgProp`, the
    -- client's result predicate for each entry: a proposal's atomic update is now
    -- deposited before the proposal reaches `Step` (`prop_deposit`), and its entries'
    -- `isMessage` says so (`entData`).)
    (ents : List raftpb.Entry)
    -- (2026-10-12) the list the message's `Context` holds, which the abstract message
    -- carries (a heartbeat's response echoes it; a forwarded proposal keeps it)
    (ctx : List w8),
  -- The ghost state is about one configuration, and it is this one. Without this the
  -- caller could hand `ownRaftGhost_step` a `cfg` of its own choosing -- a singleton
  -- one, say, in which the node is its own quorum -- and election safety would not
  -- hold. See `RaftNames`.
  γ.reCfg = cfg →
  StepMsg m →
  -- The node is a voter. `stepCandidate` needs this outright (its `poll` and
  -- `becomeLeader` both do) and `spec_stepCandidate_MsgVoteResp.v` says to thread it
  -- in "from the caller" -- but `Step` *is* the outermost caller, so it has to enter
  -- the development here. Under the no-learner, no-reconfiguration scope this is a
  -- property of the node, not of a particular call. Added 2026-09-16 for the
  -- `MsgVoteResp` branch.
  id ∈ cfg →
  -- A `MsgHup` is local (`Term = 0`) and may start an election, which increments the
  -- term; `send` panics if that wraps to zero.
  (m.Type' = MsgHup →
     m.Term' = W64 0 ∧
     uint.Z s.term + 1 < 2 ^ 64) →
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
  -- - (2026-10-10) a `MsgPreVote` reaches only a node with pre-vote on (the setting is
  --   the cluster's): a node with pre-vote off then never sends a pre-vote message, and
  --   every message it queues is of a term at most its own (`OutTermOk`). `RawNode.Step`
  --   takes no pre-vote message at all.
  (m.Type' = MsgPreVote →
     m.To' = id ∧ m.Term' ≠ W64 0 ∧
     m.From' ≠ W64 0 ∧ m.From' ≠ id ∧
     (s.term = W64 0 →
      plogUpToDate s.logst.prev (s.logst.sents ++ s.logst.uents)
        (entryID.mk m.LogTerm' m.Index') = true) ∧
     s.prevote = true) →
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
  (m.Type' = MsgBeat → m.Term' = W64 0) →
  (m.Type' = MsgProp →
     m.Term' = W64 0 ∧
     (m.From' = W64 0 ∨ m.From' = id)) →
  -- The two local acknowledgements `RawNode.Advance` steps (2026-10-05), as
  -- `acceptReady` builds them (`InvRawnode.lean`, `appendAckMsg`, `applyAckMsg`). A
  -- `MsgStorageAppendResp` carries no snapshot (a pending snapshot is out of `Ready`'s
  -- scope; `appliedSnap` is phase 2), is not from a later term (it would make the node
  -- step down to a term no message brought), and -- when its `stableTo` runs (`Term`
  -- `0` or current, a nonzero `Index`) -- acknowledges only persisted entries
  -- (`StableOk`: Go compares only the term at `Index`). A `MsgStorageApplyResp` is
  -- local (`Term = 0`); its entries' last index is committed (the bound is in `"Hm"`,
  -- where the list is named).
  (m.Type' = MsgStorageAppendResp →
     m.Snapshot' = null ∧
     uint.Z m.Term' ≤ uint.Z s.term ∧
     (m.Term' = W64 0 ∨ m.Term' = s.term →
      m.Index' ≠ W64 0 →
      StableOk s.logst (entryID.mk m.LogTerm' m.Index')) ∧
     -- (2026-10-10) `stableTo` may hand out every unstable entry still to come
     -- (`NGhost.unst`): `RawNode.Advance` steps it only after `acceptReady` reset the flag
     s.gh.unst = false) →
  (m.Type' = MsgStorageApplyResp → m.Term' = W64 0) →
  -- Read-index (2026-10-13): a request is unstamped (`Term = 0`; a local one from
  -- `ReadIndex`, a forwarded one from a follower), and not in a single-voter
  -- configuration (`IsSingleton`'s immediate answer is out of scope); a response is a
  -- leader's, from another node.
  (m.Type' = MsgReadIndex → m.Term' = W64 0 ∧ 1 < GMap.size cfg) →
  (m.Type' = MsgReadIndexResp →
     m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0 ∧ m.From' ≠ id) →
  -- (2026-10-13) the local reports, `ForgetLeader` and leader transfer (`RestMsgOk`)
  RestMsgOk s m →
  -- The one place the two layers meet. `s` is the physical abstract state
  -- `ownRaftPhys` is indexed by, `ps` the protocol state the ghost state is about,
  -- and `NStateRel` (`Defs.lean`) connects them: `ps` is `s`'s protocol fields,
  -- `r.step` agrees with the role, nothing is on loan.
  NStateRel s ps →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhys cfg r id s ∗
      "Hghost" ∷ ownRaftGhost γ id ps ∗
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
      "Hm" ∷ (
         "Hents" ∷ (if m.Type' = MsgProp then m.Entries' ↦* ents ∗ (∃ cs, ccEntsOk ents cs)
                    else m.Entries' ↦*□ ents) ∗
         "Hents_cap" ∷ ownSliceCap raftpb.Entry m.Entries' (DFrac.own 1) ∗
         "%Hprop" ∷ ⌜m.Type' = MsgProp →
                      ents ≠ [] ∧
                      (ents.length : Int) < 2^61⌝ ∗
         "%Happly" ∷ ⌜m.Type' = MsgStorageApplyResp →
                       ∀ e, ents.getLast? = some e →
                       uint.Z e.Index' ≤ uint.Z s.logst.committed⌝ ∗
         "#Hmsg" ∷ □ (∀ ty, ⌜mtypeOf m.Type' = some ty⌝ -∗
                            ⌜ty ≠ .snap⌝ -∗
                            isMessage γ (absMsg ty m ents ctx))) ∗
      -- the `Context`. (Until 2026-10-13 not the leader-transfer marker -- a transfer's
      -- vote request is now an ordinary one: with `checkQuorum` off its `force` changes
      -- nothing -- and empty on a heartbeat response; a read-index position is now what
      -- `isMessage` says it is.)
      "#Hctx" ∷ m.Context' ↦*□ ctx ∗
      -- (2026-10-13) a read-index request carries a read credit (`rdOwn`)
      "Hcred" ∷ rdCred γ (if m.Type' = MsgReadIndex then 1 else 0) ∗
      -- A `MsgSnap`'s snapshot (2026-10-02): what `m.Snapshot` points to, read-only,
      -- and the list behind its `ConfState.Voters`; under the fixed-voter-set scope
      -- `SnapScope` (`Spec/raft__restore.lean`): the voters are `cfg`'s, `cfg` is
      -- zero-free, the other three sets are empty and `AutoLeave` is off (what
      -- `confchange.Restore`'s and `assertConfStatesEquivalent`'s specs cover), and
      -- the index is below `2^61` (a pending snapshot becomes the `Storage`'s
      -- boundary, which `isStorage`'s `Hbounded` bounds the same way). And the
      -- abstraction `absSnap` (`Defs.lean`) -- the snapshot's metadata, not `m`'s own
      -- `Index`/`LogTerm` -- was legitimately sent. The two added on 2026-10-02 with
      -- the branch (`W64 0 ∉ cfg`, `AutoLeave`, the index bound) are transport/client
      -- assumptions like the rest.
      "#Hsnap" ∷ □ (⌜m.Type' = MsgSnap⌝ -∗
         ∃ (sv : raftpb.Snapshot) (voters : List w64),
           m.Snapshot' ↦□ sv ∗
           sv.Metadata'.ConfState'.Voters' ↦*□ voters ∗
           ⌜SnapScope cfg sv voters⌝ ∗
           isMessage γ (absSnap m sv voters)) }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
  {{ (err : GoInterface) (s' : NState) (ps' : PState), RET #err;
      "Hphys" ∷ ownRaftPhys cfg r id s' ∗
      "Hghost" ∷ ownRaftGhost γ id ps' ∗
      "%Hrel" ∷ ⌜NStateRel s' ps'⌝ ∗
      "%Hrefines" ∷ ⌜∃ recv, Step cfg id ps recv ps'⌝ ∗
      -- for the local messages `RawNode` steps, what is kept of the physical state
      -- (2026-10-09)
      "%Hlocal" ∷ ⌜LocalStepOk m ents s s'⌝ ∗
      -- for every other message but a snapshot, what is kept of the log (2026-10-09)
      "%Hframe" ∷ ⌜m.Type' ≠ MsgSnap → m.Type' ≠ MsgStorageApplyResp → NetFrame s s'⌝ ∗
      -- and how the term moves (2026-10-09)
      "%Hterm" ∷ ⌜m.Type' ≠ MsgSnap → TermStep m s s'⌝ ∗
      -- and what a response does to the role and the term (2026-10-10)
      "%Hresp" ∷ ⌜RespStep m s s'⌝ ∗
      -- only a proposal can be dropped, with `ErrProposalDropped`
      "Herr" ∷ (⌜err = interface.nil⌝ ∨
                (⌜m.Type' = MsgProp⌝ ∗
                 globalAddr ErrProposalDropped ↦□ err)) }}

end spec

end EtcdGrove
end Perennial
