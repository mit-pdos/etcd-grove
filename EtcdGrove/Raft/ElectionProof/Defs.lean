/-
Port of `election_proof/defs.v`: shared vocabulary for the election proof.

Lean notes: the Rocq records `logstate.t` and `nstate.t` are `LogState` and `NState`;
the Rocq tactics `w32_ne` and `intros_ambient` have no counterpart (`decide` and the
section variables do their jobs).
-/
import EtcdGrove.Raft.Base
import EtcdGrove.Raft.ElectionProof.Protocol

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-! ## Message-type constants, as Lean values

`raftpb.MessageType` is a `w32`; the Goose constants are opaque `val`s, so we name the
underlying numbers. -/

def MsgHup : w32 := W32 0
def MsgApp : w32 := W32 3
def MsgAppResp : w32 := W32 4
def MsgVote : w32 := W32 5
def MsgVoteResp : w32 := W32 6
def MsgSnap : w32 := W32 7
def MsgHeartbeat : w32 := W32 8
def MsgPreVote : w32 := W32 17
def MsgPreVoteResp : w32 := W32 18
def MsgStorageAppendResp : w32 := W32 20

def StateFollower : w64 := W64 0
def StateCandidate : w64 := W64 1
def StateLeader : w64 := W64 2

section consts
variable [FfiSyntax]

def campaignElection : CampaignType := go!"CampaignElection"
def campaignPreElection : CampaignType := go!"CampaignPreElection"
def campaignTransfer : CampaignType := go!"CampaignTransfer"

end consts

def VotePending : w8 := W8 1
def VoteLost : w8 := W8 2
def VoteWon : w8 := W8 3

def stateW64 : Role → w64
  | .follower => StateFollower
  | .candidate => StateCandidate
  | .leader => StateLeader

/-! ## Abstraction of physical messages

Only election-related message types have an abstraction. -/

def mtypeOf (t : w32) : Option MsgType :=
  if t = MsgVote then some .vote
  else if t = MsgVoteResp then some .voteResp
  else if t = MsgApp then some .app
  else if t = MsgHeartbeat then some .heartbeat
  else none

theorem mtypeOf_MsgVote : mtypeOf MsgVote = some .vote := by
  simp [mtypeOf]

theorem mtypeOf_MsgVoteResp : mtypeOf MsgVoteResp = some .voteResp := by
  simp [mtypeOf, MsgVoteResp, MsgVote]

section msgs
variable [FfiSyntax]

def absMsg (ty : MsgType) (m : raftpb.Message) : Msg :=
  ⟨ty, m.From', m.To', m.Term', m.Reject'⟩

/-- The partial abstraction of a physical message: `none` for the message types the
election model does not describe. `MsgAppResp` is the one that matters —
`appendEntry` queues one, so a total abstraction would make the abstract outbox
undefined exactly where `becomeLeader` needs it. -/
def absMsgOpt (m : raftpb.Message) : Option Msg :=
  (mtypeOf m.Type').map (absMsg · m)

theorem absMsgOpt_some (ty : MsgType) (m : raftpb.Message) (H : mtypeOf m.Type' = some ty) :
    absMsgOpt m = some (absMsg ty m) := by
  simp [absMsgOpt, H]

/-- What `Step.win` demands of a winner's broadcast: any list of `App` messages from
`id` at the given term, possibly empty. Lives here rather than in `StepLemmas.lean`
because `InvRaftPhys.lean`'s `bcastAppend` axiom needs it, and it does not mention
`cfg`. -/
def AppSends (id term : w64) (ms : List Msg) : Prop :=
  ∀ m ∈ ms, m.ty = .app ∧ m.src = id ∧ m.term = term

/-- The abstract outbox of the two physical queues, together. -/
def absOutbox (msgs msgsAA : List raftpb.Message) : List Msg :=
  msgs.filterMap absMsgOpt ++ msgsAA.filterMap absMsgOpt

/-- `send` appends to one queue or the other depending on the message type. The
abstract outbox grows at the end either way — but only up to permutation, which is
why `ownRaftPhys` relates the two with `≡ₚ`. -/
theorem absOutbox_snoc_msgs (msgs msgsAA : List raftpb.Message) (m : raftpb.Message)
    (ty : MsgType) (H : mtypeOf m.Type' = some ty) :
    absOutbox (msgs ++ [m]) msgsAA ≡ₚ absOutbox msgs msgsAA ++ [absMsg ty m] := by
  simp only [absOutbox, List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
    absMsgOpt_some ty m H, List.append_assoc]
  exact List.Perm.append_left _ (List.perm_append_comm (l₁ := [_]))

theorem absOutbox_snoc_msgsAA (msgs msgsAA : List raftpb.Message) (m : raftpb.Message)
    (ty : MsgType) (H : mtypeOf m.Type' = some ty) :
    absOutbox msgs (msgsAA ++ [m]) ≡ₚ absOutbox msgs msgsAA ++ [absMsg ty m] := by
  simp [absOutbox, List.filterMap_append, absMsgOpt_some ty m H, List.append_assoc]

/-- A message the model does not describe leaves the abstract outbox alone. -/
theorem absOutbox_snoc_msgsAA_none (msgs msgsAA : List raftpb.Message) (m : raftpb.Message)
    (H : mtypeOf m.Type' = none) :
    absOutbox msgs (msgsAA ++ [m]) = absOutbox msgs msgsAA := by
  simp [absOutbox, List.filterMap_append, absMsgOpt, H]

end msgs

/-! ## The abstract state of a `raftLog`

What every `raftLog` spec is stated at.
* `prev`, `sents`, `uents`: the entry list.
* `committed`, `applied`: `l.committed` and `l.applied`. Nothing on the election path
  writes them; they are in the state because `hasUnappliedConfChanges` and
  `maybeSendAppend` read them and a spec has to be able to say what was read.

Every field is physical (main's notes/decisions.md, "One predicate per object", and
2026-09-29). -/

structure LogState [FfiSyntax] where
  prev : entryID
  sents : List raftpb.Entry
  uents : List raftpb.Entry
  committed : w64
  applied : w64

section logstate
variable [FfiSyntax]

/-! ### Physical transitions of the log

`logLast ls` is `lastIndex()` of a log at `ls`, as a `w64`; the `raftLog` specs return
it as an `Int` equation, and `ownRaftLog`'s `Hnowrap` says the `W64` does not wrap. -/

def logLast (ls : LogState) : w64 :=
  W64 (uint.Z ls.prev.index' + ls.sents.length + ls.uents.length)

/-- `raftLog.append` at the end of the log: the batch joins the unstable suffix. -/
def logAppend (ls : LogState) (ents : List raftpb.Entry) : LogState :=
  { ls with uents := ls.uents ++ ents }

/-- `appendEntry`'s stamping loop: `es[k].Term = r.Term` and `es[k].Index = li+1+k`;
nothing else about an entry changes, which is what keeps `Type = EntryNormal` true of
the appended entries. -/
def stamp (tm li : w64) (k : Nat) (e : raftpb.Entry) : raftpb.Entry :=
  { e with Term' := tm, Index' := li + W64 1 + W64 k }

end logstate

/-! ## The physical abstract state

`NState` is what `ownRaftPhys r id s` (`InvRaftPhys.lean`) is indexed by: the **most
abstract description of the raft struct and the heap hanging off it that still lets
every Go-level spec be stated on `ownRaftPhys` alone**. It is the first of three layers
(main's notes/decisions.md, "Three layers"):

    Go code and heap  --ownRaftPhys-->  NState
    NState            --NStateRel---->  PState (Protocol.lean)
    PState            --ownRaftGhost->  protocol properties

**The rule.** If a function cannot be specified with `ownRaftPhys`, refine `NState`
(and `ownRaftPhys` with it) until it can. Do *not* introduce a variant predicate -- a
second ownership predicate for the struct, or one with an extra parameter -- for one
caller's benefit. The fields that are not protocol state:

* `stepfn` is `r.step`. `becomeFollower` writes it *before* calling `reset`, and
  `newRaft` calls `becomeFollower` while it is still nil, so it cannot be a function
  of `role`.
* `progress` is the progress map, id to `*Progress`. Nothing on the election path
  inserts into or deletes from it, so it is stable across every call.
* `prvals` is each peer's `Progress` *value*, with its `Inflights` value: what `*pr`
  and `*pr.Inflights` hold for the `pr` that `progress` maps the peer to. `ownTracker`
  is indexed by it (`InvTracker.lean`).
* `log` is `r.raftLog`, the log's location (it never changes).
* `logst` is the log's state (`LogState`).

The first six fields are exactly `PState`'s, with the same names. -/

structure NState [FfiSyntax] where
  term : w64
  vote : w64
  lead : w64
  role : Role
  votes : GMap w64 Bool
  outbox : List Msg
  /-- `r.step` -/
  stepfn : GoFunc
  /-- `r.trk.Progress`, as a map -/
  progress : GMap w64 Loc
  /-- `r.raftLog` -/
  log : Loc
  /-- the log's abstract state -/
  logst : LogState
  /-- `*pr`, `*pr.Inflights`, per peer -/
  prvals : GMap w64 (tracker.Progress × tracker.Inflights)

section phys_state
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- Which of the three `stepX` functions `r.step` holds in each role. The `becomeX`
functions assign these, and `Step` dispatches a message it does not handle inline
through `r.step(m)`. -/
def stepFuncOf : Role → GoFunc
  | .follower => functions stepFollower []
  | .candidate => functions stepCandidate []
  | .leader => functions stepLeader []

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
  { resetTo s term with lead := lead, role := .follower, stepfn := stepFuncOf .follower }

def becomeCandidate (id : w64) (s : NState) : NState :=
  { resetTo s (s.term + W64 1) with vote := id, role := .candidate,
                                    stepfn := stepFuncOf .candidate }

/-- `becomeLeader` up to its `appendEntry`: what `reset`, the `lead` and `state`
writes and `r.step` leave. -/
def becomeLeaderPre (id : w64) (s : NState) : NState :=
  { resetTo s s.term with lead := id, role := .leader, stepfn := stepFuncOf .leader }

/-- The empty entry a new leader appends (`pb.Entry{Data: nil}`, the zero `Entry`),
stamped at the leader's term and the log's next index. -/
def leaderEntry (s : NState) : raftpb.Entry :=
  stamp s.term (logLast s.logst) 0 (zero_val raftpb.Entry)

/-- `becomeLeader`: `becomeLeaderPre`, then the empty entry appended. -/
def becomeLeader (id : w64) (s : NState) : NState :=
  { becomeLeaderPre id s with logst := logAppend s.logst [leaderEntry s] }

/-! ### The connection to the protocol state -/

def toPState (s : NState) : PState :=
  ⟨s.term, s.vote, s.lead, s.role, s.votes, s.outbox⟩

/-- A physical state that can take a protocol step: `r.step` agrees with the role.
Every `becomeX` establishes it. -/
def NStateWf (s : NState) : Prop := s.stepfn = stepFuncOf s.role

/-- `s` refines the protocol state `ps`. -/
def NStateRel (s : NState) (ps : PState) : Prop := toPState s = ps ∧ NStateWf s

/-! Each physical transition is its protocol counterpart on `toPState`. All by
computation; stated so that proofs rewrite rather than unfold. -/

theorem toPState_sendMsgs (s : NState) (ms : List Msg) :
    toPState (sendMsgs s ms) = psendMsgs (toPState s) ms := rfl

theorem toPState_becomeFollower (s : NState) (term lead : w64) :
    toPState (becomeFollower s term lead) = pbecomeFollower (toPState s) term lead := rfl

/-- `reset`'s conditional clear of the vote is overwritten by `vote := id`. -/
theorem toPState_becomeCandidate (id : w64) (s : NState) :
    toPState (becomeCandidate id s) = pbecomeCandidate id (toPState s) := rfl

theorem toPState_becomeLeader (id : w64) (s : NState) :
    toPState (becomeLeader id s) = pbecomeLeader id (toPState s) := by
  simp [becomeLeader, becomeLeaderPre, resetTo, toPState, pbecomeLeader]

theorem toPState_votes (s : NState) (v : GMap w64 Bool) :
    toPState { s with votes := v } = { toPState s with votes := v } := rfl

theorem toPState_vote (s : NState) (v : w64) :
    toPState { s with vote := v } = { toPState s with vote := v } := rfl

theorem nstateWf_becomeFollower (s : NState) (term lead : w64) :
    NStateWf (becomeFollower s term lead) := rfl

theorem nstateWf_becomeCandidate (id : w64) (s : NState) :
    NStateWf (becomeCandidate id s) := rfl

theorem nstateWf_becomeLeader (id : w64) (s : NState) : NStateWf (becomeLeader id s) := rfl

/-- A state with new `Progress` values is as well-formed as before: `r.step` and the
role are untouched. -/
theorem nstateWf_prvals (s : NState) (pvs : GMap w64 (tracker.Progress × tracker.Inflights))
    (H : NStateWf s) : NStateWf { s with prvals := pvs } := H

theorem toPState_prvals (s : NState) (pvs : GMap w64 (tracker.Progress × tracker.Inflights)) :
    toPState { s with prvals := pvs } = toPState s := rfl

theorem nstateWf_sendMsgs (s : NState) (ms : List Msg) (H : NStateWf s) :
    NStateWf (sendMsgs s ms) := H

end phys_state

end EtcdGrove
end Perennial
