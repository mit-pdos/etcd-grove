/- Port of election_proof/spec_stepCandidate.v (feb5c73d4).

## `stepCandidate`, for the message types in scope

`stepCandidate.impl` (`Code/go_etcd_io/raft/v3.lean`; raft.go:1660) first
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
module

public import Spec.go_etcd_io.raft.v3.raft__handleAppendEntries
public import Spec.go_etcd_io.raft.v3.raft__handleHeartbeat
public import Spec.go_etcd_io.raft.v3.raft__handleSnapshot
public import Proof.go_etcd_io.raft.v3.StepLemmas

@[expose] public section

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
    (ents : List raftpb.Entry) (sv : raftpb.Snapshot) (dropped : Bool) (s' : NState)
    (cl : List w8 := []) : Prop :=
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
      { becomeFollower s s.term m.From' with prvals := pvs } m cl
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
  -- read-index (2026-10-12): no case, nothing happens
  else if m.Type' = MsgReadIndex ∨ m.Type' = MsgReadIndexResp then dropped = false ∧ s' = s
  -- (2026-10-13) likewise; `MsgTimeoutNow` is logged and ignored
  else if m.Type' = MsgForgetLeader ∨ m.Type' = MsgTransferLeader ∨ m.Type' = MsgTimeoutNow ∨
      m.Type' = MsgUnreachable ∨ m.Type' = MsgSnapStatus then dropped = false ∧ s' = s
  else False

/-- `CandVoteRespResult` at the configuration `c` (2026-10-13, reconfiguration stage A2): `poll`'s
facts are joint (`JQuorum`, `JLost`). -/
def CandVoteRespResultC (c : CfgM) (id : w64) (s : NState) (m : raftpb.Message)
    (s' : NState) : Prop :=
  ∃ (won lost : Bool) (ms : List Msg) (pvs : GMap w64 Progress),
    let votes' := recordVote s.votes m.From' (!m.Reject')
    (won = true →
       JQuorum c (granted votes') ∧
       ReplSends id (becomeLeader id { s with votes := votes' }) ms ∧
       prvalsMatch pvs = resetMatched id (logLast s.logst) s.prvals) ∧
    (lost = true → JLost c votes') ∧
    s' = { voteRespResult id s m.From' m.Reject' won lost ms with prvals := pvs }

/-- `PrecandVoteRespResult` at the configuration `c`: the joint facts, and on a win the peers
`campaign` asked, the other voters of either half. -/
def PrecandVoteRespResultC (c : CfgM) (id : w64) (s : NState) (m : raftpb.Message)
    (s' : NState) : Prop :=
  ∃ (won lost : Bool) (peers : List w64) (pvs : GMap w64 Progress),
    let votes' := recordVote s.votes m.From' (!m.Reject')
    (won = true → JQuorum c (granted votes') ∧ peers ≡ₚ elements (c.voters \ {[id]})) ∧
    (lost = true → JLost c votes') ∧
    s' = { prevoteRespResult id s m.From' m.Reject' won lost peers with prvals := pvs }

/-- `CandidateStepResult` at the configuration `c` (2026-10-13, reconfiguration stage A2), with the
configuration `c'` the node is at afterwards (`c`, but the snapshot's after a `MsgSnap` that
`restore` installs: since 2026-10-14, stage A3, with any voters `scfg`, `SnapCfgOk`). -/
def CandidateStepResultC (c : CfgM) (scfg : GSet w64) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) (sv : raftpb.Snapshot) (dropped : Bool) (s' : NState)
    (c' : CfgM) (cl : List w8 := []) : Prop :=
  (if m.Type' = MsgSnap then SnapCfgOk c scfg s sv s' c'
   else c' = c) ∧
  (if m.Type' = MsgVoteResp then
       dropped = false ∧
       (if s.role = .preCandidate then s' = s
        else CandVoteRespResultC c id s m s')
     else if m.Type' = MsgProp then dropped = true ∧ s' = s
     else if m.Type' = MsgApp then
       dropped = false ∧
       ∃ (pvs : GMap w64 Progress), HandleAppResult id
         { becomeFollower s s.term m.From' with prvals := pvs } m ents s'
     else if m.Type' = MsgHeartbeat then
       dropped = false ∧
       ∃ (pvs : GMap w64 Progress), s' = heartbeatResult id
         { becomeFollower s s.term m.From' with prvals := pvs } m cl
     else if m.Type' = MsgBeat ∨ m.Type' = MsgAppResp ∨ m.Type' = MsgHeartbeatResp then
       dropped = false ∧ s' = s
     else if m.Type' = MsgSnap then
       dropped = false ∧
       ∃ (pvs : GMap w64 Progress), HandleSnapResult id
         { becomeFollower s s.term m.From' with prvals := pvs } m sv s'
     else if m.Type' = MsgPreVoteResp then
       dropped = false ∧
       (if s.role = .preCandidate then PrecandVoteRespResultC c id s m s'
        else s' = s)
     else if m.Type' = MsgReadIndex ∨ m.Type' = MsgReadIndexResp then dropped = false ∧ s' = s
     else if m.Type' = MsgForgetLeader ∨ m.Type' = MsgTransferLeader ∨ m.Type' = MsgTimeoutNow ∨
         m.Type' = MsgUnreachable ∨ m.Type' = MsgSnapStatus then dropped = false ∧ s' = s
     else False)

theorem CandVoteRespResultC.simple {cfg L : GSet w64} {id : w64} {s : NState} {m : raftpb.Message}
    {s' : NState} (hne : cfg ≠ ∅) (h : CandVoteRespResultC (CfgM.simple cfg L) id s m s') :
    CandVoteRespResult cfg id s m s' := by
  obtain ⟨won, lost, ms, pvs, h1, h2, h3⟩ := h
  refine ⟨won, lost, ms, pvs, fun hw => ?_, fun hl => ?_, h3⟩
  · obtain ⟨a, b, c⟩ := h1 hw
    exact ⟨(JQuorum_of_out (c := CfgM.simple cfg L) hne rfl _).1 a, b, c⟩
  · exact (JLost_of_out (c := CfgM.simple cfg L) hne rfl _).1 (h2 hl)

theorem PrecandVoteRespResultC.simple {cfg L : GSet w64} {id : w64} {s : NState} {m : raftpb.Message}
    {s' : NState} (hne : cfg ≠ ∅) (h : PrecandVoteRespResultC (CfgM.simple cfg L) id s m s') :
    PrecandVoteRespResult cfg id s m s' := by
  obtain ⟨won, lost, peers, pvs, h1, h2, h3⟩ := h
  refine ⟨won, lost, peers, pvs, fun hw => ?_, fun hl => ?_, h3⟩
  · obtain ⟨a, b⟩ := h1 hw
    refine ⟨(JQuorum_of_out (c := CfgM.simple cfg L) hne rfl _).1 a, ?_⟩
    rw [CfgM.voters_simple] at b; exact b
  · exact (JLost_of_out (c := CfgM.simple cfg L) hne rfl _).1 (h2 hl)

theorem CandidateStepResultC.simple {cfg L scfg : GSet w64} {id : w64} {s : NState}
    {m : raftpb.Message}
    {ents : List raftpb.Entry} {sv : raftpb.Snapshot} {dropped : Bool} {s' : NState} {c' : CfgM}
    {cl : List w8} (hne : cfg ≠ ∅)
    (h : CandidateStepResultC (CfgM.simple cfg L) scfg id s m ents sv dropped s' c' cl) :
    CandidateStepResult cfg id s m ents sv dropped s' cl := by
  obtain ⟨-, h⟩ := h
  unfold CandidateStepResult
  by_cases hV : m.Type' = MsgVoteResp
  · simp only [hV, ↓reduceIte] at h ⊢
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    split at h2
    · rename_i hp; simp only [hp, ↓reduceIte]; exact h2
    · rename_i hp; simp only [hp, ↓reduceIte]; exact h2.simple hne
  by_cases hP : m.Type' = MsgPreVoteResp
  · simp [hP, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat, MsgAppResp, MsgHeartbeatResp,
      MsgSnap, MsgPreVoteResp] at h ⊢
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    split at h2
    · rename_i hp; simp only [hp, ↓reduceIte]; exact h2.simple hne
    · rename_i hp; simp only [hp, ↓reduceIte]; exact h2
  simp only [hV, hP, if_false] at h ⊢
  exact h

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
  r.Term`"), and it is nonzero (2026-10-10: a win's `becomeLeader` stamps its
  self-acknowledgement with it);
- `id ∈ cfg`: a candidate that can win is a voter; `poll` needs `cfg` non-empty and
  `becomeLeader` needs this outright, and neither is available from `ownRaftPhys`, so
  it is threaded in from the caller;
- `MsgApp`: `handleAppendEntries`'s premises, at `s` (`becomeFollower` leaves the log
  alone); a `MsgSnap`, likewise, from another node;
- `MsgHeartbeat`: `handleHeartbeat`'s premises, at `s` (likewise): `m.Commit` within
  the log and `m.From ≠ id`;
- `Hents`: the `Entries` slice and its capacity, for `MsgApp` only;
- a pre-candidate's `MsgPreVoteResp`: the term does not wrap, since a win runs
  `campaign`, which increments it. 

At any configuration since 2026-10-13 (reconfiguration stage A2): the struct at `c`
(`ownRaftPhysCV c c.voters`), `poll`'s facts joint, a pre-vote win's campaign over the voters
of either half (`CandidateStepResultC`); a `MsgSnap` (since 2026-10-14, stage A3) at any `c`, of
a snapshot whose configuration is non-joint with any voters `scfg` containing the node, after
which the node is at the snapshot's configuration if `restore` installed it (until then: only
at a non-joint `c`, `scfg = c.incoming`); in the A2 wording: a `MsgSnap` only at a non-joint `c`, after which the
node is at the snapshot's configuration. The old statement is `stepCandidate.specS`.
-/
abbrev stepCandidate.spec : Prop :=
  ∀ (c : CfgM) (scfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) (sv : raftpb.Snapshot) (voters : List w64) (cl : List w8),
  (m.Type' = MsgVoteResp ∨ m.Type' = MsgProp ∨
   m.Type' = MsgApp ∨ m.Type' = MsgHeartbeat ∨
   (m.Type' = MsgBeat ∨ m.Type' = MsgAppResp ∨ m.Type' = MsgHeartbeatResp) ∨
   m.Type' = MsgSnap ∨ m.Type' = MsgPreVoteResp ∨
   m.Type' = MsgReadIndex ∨
   (m.Type' = MsgReadIndexResp ∨ m.Type' = MsgForgetLeader ∨ m.Type' = MsgTransferLeader ∨
    m.Type' = MsgTimeoutNow ∨ m.Type' = MsgUnreachable ∨ m.Type' = MsgSnapStatus)) →
  (m.Type' = MsgVoteResp ∨ m.Type' = MsgApp ∨
   m.Type' = MsgHeartbeat ∨ m.Type' = MsgSnap →
   m.Term' = s.term ∧ m.Term' ≠ W64 0) →
  s.role = .candidate ∨ s.role = .preCandidate →
  (m.Type' = MsgApp →
     PlogWf (entryID.mk m.LogTerm' m.Index') ents ∧
     uint.Z m.Index' + (ents.length : Int) + 1 < 2^64 ∧
     (let ls := s.logst
      let es := ls.sents ++ ls.uents
      uint.Z ls.committed ≤ uint.Z m.Index' →
      PlogMatches ls.prev es (entryID.mk m.LogTerm' m.Index') →
      plogFindConflict ls.prev es ents = W64 0 ∨
      uint.Z ls.committed < uint.Z (plogFindConflict ls.prev es ents)) ∧
     -- from another node (2026-10-10, `handleAppendEntries`'s premise)
     m.From' ≠ id) →
  (m.Type' = MsgHeartbeat →
     uint.Z m.Commit' ≤ plogLastIndexZ s.logst.prev (s.logst.sents ++ s.logst.uents) ∧
     m.From' ≠ id) →
  (s.role = .preCandidate → m.Type' = MsgPreVoteResp →
   uint.Z s.term + 1 < 2 ^ 64) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      -- the `Context` (2026-10-12): what the response to a heartbeat carries
      "Hctx" ∷ (⌜m.Type' = MsgHeartbeat⌝ -∗ m.Context' ↦*□ cl) ∗
      "Hsnap" ∷ (⌜m.Type' = MsgSnap⌝ -∗
                 ∃ learners, ⌜SnapScope scfg sv voters learners ∧ id ∈ scfg ∧
                   m.From' ≠ id⌝ ∗
                 m.Snapshot' ↦□ sv ∗
                 sv.Metadata'.ConfState'.Voters' ↦*□ voters ∗
                 ownIdList sv.Metadata'.ConfState'.Learners' DFrac.discard learners) ∗
      "Hents" ∷ (⌜m.Type' = MsgApp⌝ -∗
                 m.Entries' ↦*□ ents ∗
                 ownSliceCap raftpb.Entry m.Entries' (DFrac.own 1)) }}
    (App (App (Val #(functions stepCandidate [])) (Val #r)) (Val #m))
  {{ (err : GoInterface) (s' : NState) (dropped : Bool) (c' : CfgM), RET #err;
      ownRaftPhysCV c' c'.voters r id s' ∗
      ⌜CandidateStepResultC c scfg id s m ents sv dropped s' c' cl⌝ ∗
      (if dropped then globalAddr ErrProposalDropped ↦□ err
       else ⌜err = interface.nil⌝) }}

/-- The statement on `ownRaftPhys` (the simple configuration `cfg`) until 2026-10-13,
derived from `stepCandidate.spec` by `stepCandidate.spec_simple`. -/
abbrev stepCandidate.specS : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) (sv : raftpb.Snapshot) (voters : List w64) (cl : List w8),
  (m.Type' = MsgVoteResp ∨ m.Type' = MsgProp ∨
   m.Type' = MsgApp ∨ m.Type' = MsgHeartbeat ∨
   (m.Type' = MsgBeat ∨ m.Type' = MsgAppResp ∨ m.Type' = MsgHeartbeatResp) ∨
   m.Type' = MsgSnap ∨ m.Type' = MsgPreVoteResp ∨
   m.Type' = MsgReadIndex ∨
   (m.Type' = MsgReadIndexResp ∨ m.Type' = MsgForgetLeader ∨ m.Type' = MsgTransferLeader ∨
    m.Type' = MsgTimeoutNow ∨ m.Type' = MsgUnreachable ∨ m.Type' = MsgSnapStatus)) →
  (m.Type' = MsgVoteResp ∨ m.Type' = MsgApp ∨
   m.Type' = MsgHeartbeat ∨ m.Type' = MsgSnap →
   m.Term' = s.term ∧ m.Term' ≠ W64 0) →
  s.role = .candidate ∨ s.role = .preCandidate →
  (m.Type' = MsgApp →
     PlogWf (entryID.mk m.LogTerm' m.Index') ents ∧
     uint.Z m.Index' + (ents.length : Int) + 1 < 2^64 ∧
     (let ls := s.logst
      let es := ls.sents ++ ls.uents
      uint.Z ls.committed ≤ uint.Z m.Index' →
      PlogMatches ls.prev es (entryID.mk m.LogTerm' m.Index') →
      plogFindConflict ls.prev es ents = W64 0 ∨
      uint.Z ls.committed < uint.Z (plogFindConflict ls.prev es ents)) ∧
     m.From' ≠ id) →
  (m.Type' = MsgHeartbeat →
     uint.Z m.Commit' ≤ plogLastIndexZ s.logst.prev (s.logst.sents ++ s.logst.uents) ∧
     m.From' ≠ id) →
  (s.role = .preCandidate → m.Type' = MsgPreVoteResp →
   uint.Z s.term + 1 < 2 ^ 64) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhys cfg r id s ∗
      "Hctx" ∷ (⌜m.Type' = MsgHeartbeat⌝ -∗ m.Context' ↦*□ cl) ∗
      "Hsnap" ∷ (⌜m.Type' = MsgSnap⌝ -∗
                 ∃ learners, ⌜SnapScope cfg sv voters learners ∧ m.From' ≠ id⌝ ∗
                 m.Snapshot' ↦□ sv ∗
                 sv.Metadata'.ConfState'.Voters' ↦*□ voters ∗
                 ownIdList sv.Metadata'.ConfState'.Learners' DFrac.discard learners) ∗
      "Hents" ∷ (⌜m.Type' = MsgApp⌝ -∗
                 m.Entries' ↦*□ ents ∗
                 ownSliceCap raftpb.Entry m.Entries' (DFrac.own 1)) }}
    (App (App (Val #(functions stepCandidate [])) (Val #r)) (Val #m))
  {{ (err : GoInterface) (s' : NState) (dropped : Bool), RET #err;
      ownRaftPhys cfg r id s' ∗
      ⌜CandidateStepResult cfg id s m ents sv dropped s' cl⌝ ∗
      (if dropped then globalAddr ErrProposalDropped ↦□ err
       else ⌜err = interface.nil⌝) }}

open Iris.ProofMode in
theorem stepCandidate.spec_simple
    (H : stepCandidate.spec (GF := GF) (hG := hG)) :
    stepCandidate.specS (GF := GF) (hG := hG) := by
  intro cfg r id s m ents sv voters cl Hty Hterm Hrole Happ Hhb Hpvnw
  iintro %Φ ⟨#Hpkg, Hphys, Hctx, Hsnap, Hents⟩ HΦ
  icases ownRaftPhys_voter cfg r id s $$ Hphys with ⟨%Hv, Hphys⟩
  have Hin : id ∈ cfg := Hv (by rcases Hrole with h | h <;> rw [h] <;> decide)
  have Hne : cfg ≠ ∅ := fun h => GMap.not_elem_of_empty id (h ▸ Hin)
  ihave Hphys := ownRaftPhys_toC' $$ Hphys
  iapply H (CfgM.simple cfg (domSet s.progress \ cfg)) cfg r id s m ents sv voters cl Hty Hterm
      Hrole Happ Hhb Hpvnw
    $$ [$Hpkg $Hphys $Hctx Hsnap $Hents]
  · iintro %Hm
    icases Hsnap $$ %Hm with ⟨%learners, %Hsc, Hsv⟩
    iexists learners
    iframe Hsv
    ipureintro
    exact ⟨Hsc.1, Hin, Hsc.2⟩
  inext
  iintro %err %s' %dropped %c' ⟨Hphys, %Hres, Hdr⟩
  have Hc' := Hres.1
  have Hcs : ∃ L, c' = CfgM.simple cfg L := by
    split at Hc'
    · rcases Hc' with ⟨-, h⟩ | ⟨-, h⟩
      · exact ⟨_, h⟩
      · exact ⟨_, h⟩
    · exact ⟨_, Hc'⟩
  obtain ⟨L, rfl⟩ := Hcs
  ihave Hphys := ownRaftPhysC_toS $$ Hphys
  iapply HΦ $$ %err %s' %dropped
  iframe Hphys Hdr
  ipureintro
  exact Hres.simple Hne

end spec

end EtcdGrove
end Perennial
