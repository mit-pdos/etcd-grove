/- Port of election_proof/spec_stepCandidate.v (feb5c73d4).

## `stepCandidate`, for the message types in scope

`stepCandidate.impl` (`EtcdRaft/Code/go_etcd_io/raft/v3.lean`; raft.go:1660) first
reads `r.state` to pick `myVoteRespType` (`MsgVoteResp` for a candidate,
`MsgPreVoteResp` for a pre-candidate), then switches on `m.Type`:

- `MsgProp`: `Infof`, `return ErrProposalDropped`; state unchanged.
- `MsgApp`: `becomeFollower(m.Term, m.From)` -- "always `m.Term == r.Term`", which is
  a premise here -- then `handleAppendEntries`.
- `MsgVoteResp`: at a candidate, record the vote, then win, lose or keep waiting; at a
  pre-candidate, nothing.
- `MsgPreVoteResp` (2026-10-04): at a pre-candidate, record it, then win --
  `campaign(campaignElection)`, the real election -- lose (`becomeFollower(r.Term,
  None)`) or keep waiting; at a candidate, nothing (a stale pre-vote response).
- `MsgHeartbeat`: `becomeFollower(m.Term, m.From)` -- again "always `m.Term ==
  r.Term`", a premise -- then `handleHeartbeat` (`heartbeatResult` at the follower
  state).
- `MsgBeat`, `MsgAppResp`, `MsgHeartbeatResp`: no arm (they are none of the above, nor
  `MsgSnap`, `myVoteRespType` or `MsgTimeoutNow`); nothing written, `nil`. The
  `MsgProp`, `MsgApp`, `MsgHeartbeat` and `MsgSnap` arms do not depend on the role.

Ghost-free. It used to take `ownRaftGhost` and `isMessage` for the incoming message,
but that was only ever feeding `ownRaftGhost_step`; `isMessage` is what justifies *the
model transition*, not the code, so it belongs at the one place the transition is
taken — `Step`. (Until 2026-10-01 this collection was `stepCandidate_MsgVoteResp`,
stated for `MsgVoteResp` only; that case's postcondition is unchanged.)

Lean notes:
* Rocq's `cand_vote_resp_result`, `precand_vote_resp_result` and
  `candidate_step_result` are `CandVoteRespResult`, `PrecandVoteRespResult` and
  `CandidateStepResult` (Prop-valued definitions); `if decide (P) then … else …` is
  `if P then … else …`.
* The Rocq `Section results` has the heap context (`heapGS Σ`, `go.Semantics`,
  `raft.Assumptions`) although the definitions are pure; here they need only
  `[FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]` (for `stepFuncOf`, through
  `becomeLeader`/`becomeFollower`).
-/
import EtcdGrove.Raft.Spec.raft__handleAppendEntries
import EtcdGrove.Raft.Spec.raft__handleHeartbeat
import EtcdGrove.Raft.Spec.raft__handleSnapshot
import EtcdGrove.Raft.StepLemmas

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section results
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- The `MsgVoteResp` case, as it was.

The quorum facts are **part of the spec**, not incidental. Without them this triple is
true but useless to its caller: `Step`'s `MsgVoteResp` branch has to justify the
resulting `.leader` by `Step.win`, whose premise is `IsQuorum cfg (granted …)`, and no
other `Step` rule produces a leader. `poll` establishes both facts; before 2026-09-16
the proof dropped them on the floor and `won`/`lost` escaped as unconstrained booleans.
`ms` is what `bcastAppend` broadcast on a win: what `ReplSends` allows, possibly
nothing. `recordVote` does not touch the term, so `s1`'s term is `s`'s. -/
def CandVoteRespResult (cfg : GSet w64) (id : w64) (s : NState) (m : raftpb.Message)
    (s' : NState) : Prop :=
  ∃ (won lost : Bool) (ms : List Msg) (pvs : GMap w64 Progress),
    let votes' := recordVote s.votes m.From' (!m.Reject')
    (won = true →
       IsQuorum cfg (granted votes') ∧
       -- the broadcast, judged at the new leader's state
       ReplSends id (becomeLeader id { s with votes := votes' }) ms ∧
       -- `Match` is what `becomeLeader`'s `reset` left
       prvalsMatch pvs = resetMatched id (logLast s.logst) s.prvals) ∧
    (lost = true → ¬ IsQuorum cfg (cfg \ rejected votes')) ∧
    s' = { voteRespResult id s m.From' m.Reject' won lost ms with prvals := pvs }

/-- The `MsgPreVoteResp` case at a pre-candidate (2026-10-04), `prevoteRespResult`
(`StepLemmas.lean`): `poll`'s facts as for `CandVoteRespResult`, and on a win the peers
`campaign` sent its `MsgVote`s to. The protocol needs only the latter: winning a
pre-vote proves nothing, it only starts the election (`step_prevoteRespResult`). -/
def PrecandVoteRespResult (cfg : GSet w64) (id : w64) (s : NState) (m : raftpb.Message)
    (s' : NState) : Prop :=
  ∃ (won lost : Bool) (peers : List w64) (pvs : GMap w64 Progress),
    let votes' := recordVote s.votes m.From' (!m.Reject')
    (won = true → IsQuorum cfg (granted votes') ∧ peers ≡ₚ elements (cfg \ {[id]})) ∧
    (lost = true → ¬ IsQuorum cfg (cfg \ rejected votes')) ∧
    s' = { prevoteRespResult id s m.From' m.Reject' won lost peers with prvals := pvs }

/-- What `stepCandidate` does with `m`, by type; `dropped` as in `FollowerStepResult`
(`Spec/stepFollower.lean`). For `MsgApp` the `Progress` values `becomeFollower`'s
`reset` leaves are `pvs` (unconstrained: a follower's are invisible to `toPState`). -/
def CandidateStepResult (cfg : GSet w64) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) (sv : raftpb.Snapshot) (dropped : Bool) (s' : NState) :
    Prop :=
  if m.Type' = MsgVoteResp then
    dropped = false ∧
    (if s.role = .preCandidate then s' = s
     else CandVoteRespResult cfg id s m s')
  else if m.Type' = MsgProp then dropped = true ∧ s' = s
  else if m.Type' = MsgApp then
    dropped = false ∧
    ∃ (pvs : GMap w64 Progress), HandleAppResult id
      { becomeFollower s s.term m.From' with prvals := pvs } m ents s'
  else if m.Type' = MsgHeartbeat then
    dropped = false ∧
    ∃ (pvs : GMap w64 Progress), s' = heartbeatResult id
      { becomeFollower s s.term m.From' with prvals := pvs } m
  else if m.Type' = MsgBeat ∨ m.Type' = MsgAppResp ∨ m.Type' = MsgHeartbeatResp then
    dropped = false ∧ s' = s
  else if m.Type' = MsgSnap then
    dropped = false ∧
    ∃ (pvs : GMap w64 Progress), HandleSnapResult id
      { becomeFollower s s.term m.From' with prvals := pvs } m sv s'
  else if m.Type' = MsgPreVoteResp then
    dropped = false ∧
    (if s.role = .preCandidate then PrecandVoteRespResult cfg id s m s'
     else s' = s)
  else False

end results

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- Premises:
- `s.role` is `.candidate` or `.preCandidate`: `r.step = stepCandidate` means it
  (`NStateWf`); it picks `myVoteRespType`;
- `m.Term = r.Term` for `MsgVoteResp`, `MsgApp` and `MsgHeartbeat` (`Step`'s term
  preamble has run; for the last two it is the Go comment's "always `m.Term ==
  r.Term`");
- `id ∈ cfg`: a candidate that can win is a voter; `poll` needs `cfg` non-empty and
  `becomeLeader` needs this outright, and neither is available from `ownRaftPhys`, so
  it is threaded in from the caller;
- `MsgApp`: `handleAppendEntries`'s premises, at `s` (`becomeFollower` leaves the log
  alone);
- `MsgHeartbeat`: `handleHeartbeat`'s premises, at `s` (likewise): `m.Commit` within
  the log and `m.From ≠ id`;
- `Hents`: the `Entries` slice and its capacity, for `MsgApp` only;
- a pre-candidate's `MsgPreVoteResp`: the term does not wrap, since a win runs
  `campaign`, which increments it. -/
abbrev stepCandidate.spec : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) (sv : raftpb.Snapshot) (voters : List w64),
  (m.Type' = MsgVoteResp ∨ m.Type' = MsgProp ∨
   m.Type' = MsgApp ∨ m.Type' = MsgHeartbeat ∨
   (m.Type' = MsgBeat ∨ m.Type' = MsgAppResp ∨ m.Type' = MsgHeartbeatResp) ∨
   m.Type' = MsgSnap ∨ m.Type' = MsgPreVoteResp) →
  (m.Type' = MsgVoteResp ∨ m.Type' = MsgApp ∨
   m.Type' = MsgHeartbeat ∨ m.Type' = MsgSnap →
   m.Term' = s.term) →
  s.role = .candidate ∨ s.role = .preCandidate →
  id ∈ cfg →
  (m.Type' = MsgApp →
     PlogWf (entryID.mk m.LogTerm' m.Index') ents ∧
     uint.Z m.Index' + (ents.length : Int) + 1 < 2^64 ∧
     (∀ e ∈ ents, e.Type' = EntryNormal) ∧
     (let ls := s.logst
      let es := ls.sents ++ ls.uents
      uint.Z ls.committed ≤ uint.Z m.Index' →
      PlogMatches ls.prev es (entryID.mk m.LogTerm' m.Index') →
      plogFindConflict ls.prev es ents = W64 0 ∨
      uint.Z ls.committed < uint.Z (plogFindConflict ls.prev es ents))) →
  (m.Type' = MsgHeartbeat →
     uint.Z m.Commit' ≤ plogLastIndexZ s.logst.prev (s.logst.sents ++ s.logst.uents) ∧
     m.From' ≠ id) →
  (s.role = .preCandidate → m.Type' = MsgPreVoteResp →
   uint.Z s.term + 1 < 2 ^ 64) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhys cfg r id s ∗
      "Hsnap" ∷ (⌜m.Type' = MsgSnap⌝ -∗
                 ⌜SnapScope cfg sv voters⌝ ∗
                 m.Snapshot' ↦□ sv ∗
                 sv.Metadata'.ConfState'.Voters' ↦*□ voters) ∗
      "Hents" ∷ (⌜m.Type' = MsgApp⌝ -∗
                 m.Entries' ↦*□ ents ∗
                 ownSliceCap raftpb.Entry m.Entries' (DFrac.own 1)) }}
    (App (App (Val #(functions stepCandidate [])) (Val #r)) (Val #m))
  {{ (err : GoInterface) (s' : NState) (dropped : Bool), RET #err;
      ownRaftPhys cfg r id s' ∗
      ⌜CandidateStepResult cfg id s m ents sv dropped s'⌝ ∗
      (if dropped then globalAddr ErrProposalDropped ↦□ err
       else ⌜err = interface.nil⌝) }}

end spec

end EtcdGrove
end Perennial
