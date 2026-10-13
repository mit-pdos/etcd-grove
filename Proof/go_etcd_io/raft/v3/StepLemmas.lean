/-
Port of `election_proof/step_lemmas.v` (at feb5c73d4): pure model-level lemmas and
vocabulary.

Lean notes: Rocq's `let s1 := … in` in a lemma statement is inlined.
-/
module

public import Proof.go_etcd_io.raft.v3.Defs

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

section step_lemmas
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]
-- The (fixed) set of voters.
variable (cfg : GSet w64)

/-- The outcome of feeding a `MsgVoteResp` to a candidate. `ms` is what a winner's
`bcastAppend` put on the network; it is irrelevant unless `won`. `becomeLeader`
includes `appendEntry`'s self-acknowledgement.

`ms` is whatever `ReplSends` allows rather than one `App` per peer, matching
`Step.win` — see the comment there for why the exact broadcast is not pinned down. -/
def voteRespResult (id : w64) (s : NState) (src : w64) (reject won lost : Bool)
    (ms : List Msg) : NState :=
  let s1 := { s with votes := recordVote s.votes src (!reject) }
  if won then sendMsgs (becomeLeader id s1) ms
  else if lost then becomeFollower s1 s1.term (W64 0)
  else s1

/-- The outcome of feeding a `MsgPreVoteResp` to a pre-candidate (`stepCandidate` in
`StatePreCandidate`): the tally records it, then a win starts the real election
(`campaign(campaignElection)`, whose requests go to `peers`), a loss is
`becomeFollower(r.Term, None)`, and otherwise nothing. The pre-vote tally is invisible
to the protocol (`toPState`). -/
def prevoteRespResult (id : w64) (s : NState) (src : w64) (reject won lost : Bool)
    (peers : List w64) : NState :=
  let s1 := { s with votes := recordVote s.votes src (!reject) }
  if won then campaignState id s1 false peers
  else if lost then becomeFollower s1 s1.term (W64 0)
  else s1

/-! ## Model-level lemmas justifying each branch of `Step`

Protocol facts, about `PState`: the `Step` proof applies them to `toPState s`. (Before
2026-09-22 one record served both layers.) -/

/-- The protocol reading of `voteRespResult`, with the new leader's `Match` values
`mt`. -/
def pvoteRespResult (id : w64) (ps : PState) (src : w64) (reject won lost : Bool)
    (mt : GMap w64 w64) (ms : List Msg) : PState :=
  let s1 := { ps with votes := recordVote ps.votes src (!reject) }
  if won then psendMsgs (pwinState id s1 mt) ([pselfAck id (pwinState id s1 mt)] ++ ms)
  else if lost then pbecomeFollower s1 s1.term (W64 0)
  else s1

/-- A candidate's outcome, with whatever `Progress` values the code left: `Match` is
visible only if it won. -/
theorem toPState_voteRespResult (id : w64) (s : NState) (src : w64) (reject won lost : Bool)
    (ms : List Msg) (pvs : GMap w64 Progress) (Hrc : s.role = .candidate) :
    toPState { voteRespResult id s src reject won lost ms with prvals := pvs } =
      pvoteRespResult id (toPState s) src reject won lost (prvalsMatch pvs) ms := by
  have Hr : s.role ≠ .leader := by rw [Hrc]; decide
  have Hnp : s.role ≠ .preCandidate := by rw [Hrc]; decide
  have Hps1 : toPState { s with votes := recordVote s.votes src (!reject) } =
      { toPState s with votes := recordVote (toPState s).votes src (!reject) } := by
    rw [toPState_votes _ _ Hnp, toPState_votes_nonpre _ Hnp]
  cases won <;> cases lost
  · exact (toPState_prvals_nl { s with votes := recordVote s.votes src (!reject) } pvs Hr).trans Hps1
  · exact ((toPState_prvals_nl (becomeFollower _ _ (W64 0)) pvs (by simp [becomeFollower])).trans
      (toPState_becomeFollower _ _ _)).trans (by rw [Hps1]; rfl)
  all_goals
    calc _ = psendMsgs (toPState { becomeLeader id { s with votes := recordVote s.votes src (!reject) }
            with prvals := pvs }) ms := rfl
      _ = _ := by
        rw [toPState_becomeLeader, Hps1]
        simp [pvoteRespResult, psendMsgs, List.append_assoc]

/-- `voteRespResult` keeps `NStateWf`: every outcome is a `becomeX` or leaves `r.step`
and the role alone. -/
theorem nstateWf_voteRespResult (id : w64) (s : NState) (src : w64) (reject won lost : Bool)
    (ms : List Msg) (Hsf : NStateWf s) :
    NStateWf (voteRespResult id s src reject won lost ms) := by
  unfold voteRespResult
  cases won <;> cases lost <;> simp only [Bool.false_eq_true, ↓reduceIte]
  all_goals first
    | exact Hsf
    | exact nstateWf_becomeFollower _ _ _
    | exact nstateWf_sendMsgs _ _ (nstateWf_becomeLeader _ _)

theorem nstateWf_campaignState (id : w64) (s : NState) (pre : Bool) (peers : List w64)
    (cl : List w8 := []) :
    NStateWf (campaignState id s pre peers cl) := by
  unfold campaignState; cases pre <;> exact ⟨rfl, rfl⟩

theorem nstateWf_prevoteRespResult (id : w64) (s : NState) (src : w64)
    (reject won lost : Bool) (peers : List w64) (Hsf : NStateWf s) :
    NStateWf (prevoteRespResult id s src reject won lost peers) := by
  unfold prevoteRespResult
  cases won <;> cases lost <;> simp only [Bool.false_eq_true, ↓reduceIte]
  all_goals first
    | exact Hsf
    | exact nstateWf_becomeFollower _ _ _
    | exact nstateWf_campaignState _ _ _ _ _

/-! ## Branch lemmas

These are pure facts about the protocol, independent of the program logic; the WP
proofs feed them to `ownRaftGhost_step`. -/

omit [GoGlobalContext] [GoSemanticsFunctions] in
/-- Dropping a message is always legal. -/
theorem step_drop (id : w64) (s : PState) : Step cfg id s [] s := .refl s

omit [GoGlobalContext] [GoSemanticsFunctions] in
/-- Sending pre-vote messages from oneself, one `Step.sendFree` each. -/
theorem step_send_frees (id : w64) (ps : PState) (ms : List Msg)
    (Hms : ∀ m ∈ ms, (m.ty = .preVote ∨ m.ty = .preVoteResp) ∧ m.src = id) :
    Step cfg id ps [] (psendMsgs ps ms) := by
  induction ms generalizing ps with
  | nil =>
    have : psendMsgs ps [] = ps := by simp [psendMsgs]
    rw [this]; exact .refl ps
  | cons m ms IH =>
    have Hm := Hms m (List.mem_cons_self ..)
    have Heq : psendMsgs ps (m :: ms) = psendMsgs (psendMsgs ps [m]) ms := by
      simp [psendMsgs]
    rw [Heq]
    have := Step.trans _ [] _ [] _ (Step.sendFree (cfg := cfg) ps m Hm.1 Hm.2)
      (IH (psendMsgs ps [m]) (fun m' h => Hms m' (List.mem_cons_of_mem _ h)))
    simpa using this

/-- `campaign(t)` from a non-leader: an election is `Step.campaign`; a pre-election is
`Step.abandon` (`becomePreCandidate`) followed by its `MsgPreVote`s and the
self-addressed `MsgPreVoteResp`, all free. -/
theorem step_campaignState (id : w64) (s : NState) (pre : Bool) (peers : List w64)
    (pvs : GMap w64 Progress) (Hnl : s.role ≠ .leader) (Hin : id ∈ cfg)
    (Hnw : uint.Z s.term + 1 < 2 ^ 64) (Hperm : peers ≡ₚ elements (cfg \ {[id]}))
    (cl : List w8 := []) :
    Step cfg id (toPState s) [] (toPState { campaignState id s pre peers cl with prvals := pvs }) := by
  have Hrole : (campaignState id s pre peers cl).role ≠ .leader := by
    cases pre <;> simp [campaignState, sendMsgs, becomePrecandidate, becomeCandidate]
  rw [toPState_prvals_nl (campaignState id s pre peers cl) pvs Hrole]
  cases pre
  · show Step cfg id (toPState s) [] (toPState (sendMsgs (becomeCandidate id s) _))
    rw [toPState_sendMsgs, toPState_becomeCandidate]
    exact Step.campaign (toPState s) peers cl (by rw [toPState_role]; exact proleRole_not_leader _ Hnl)
      Hin Hnw Hperm
  · show Step cfg id (toPState s) [] (toPState (sendMsgs (becomePrecandidate s) _))
    rw [toPState_sendMsgs, toPState_becomePrecandidate]
    refine Step.trans _ [] _ [] _
      (Step.abandon (cfg := cfg) (id := id) (toPState s)
        (by rw [toPState_role]; exact proleRole_not_leader _ Hnl))
      (step_send_frees cfg id _ _ ?_)
    intro m Hm
    rcases List.mem_append.1 Hm with h | h
    · simp only [List.mem_singleton] at h; subst h; exact ⟨Or.inr rfl, rfl⟩
    · simp only [List.mem_map] at h
      obtain ⟨_, _, rfl⟩ := h
      exact ⟨Or.inl rfl, rfl⟩

/-- A pre-candidate's `MsgPreVoteResp`: pending is nothing, a loss is `Step.abandon`, a
win is `Step.campaign`. -/
theorem step_prevoteRespResult (id : w64) (s : NState) (src : w64) (reject won lost : Bool)
    (peers : List w64) (pvs : GMap w64 Progress) (Hpre : s.role = .preCandidate)
    (Hin : id ∈ cfg) (Hnw : uint.Z s.term + 1 < 2 ^ 64)
    (Hperm : won = true → peers ≡ₚ elements (cfg \ {[id]})) :
    Step cfg id (toPState s) []
      (toPState { prevoteRespResult id s src reject won lost peers with prvals := pvs }) := by
  have Hs1 : toPState { s with votes := recordVote s.votes src (!reject) } = toPState s :=
    toPState_votes_pre _ _ Hpre
  have Hnl : s.role ≠ .leader := by rw [Hpre]; decide
  cases won <;> cases lost
  · show Step cfg id (toPState s) []
      (toPState { { s with votes := recordVote s.votes src (!reject) } with prvals := pvs })
    rw [toPState_prvals_nl { s with votes := recordVote s.votes src (!reject) } pvs Hnl, Hs1]
    exact .refl _
  · show Step cfg id (toPState s) []
      (toPState { becomeFollower { s with votes := recordVote s.votes src (!reject) } s.term (W64 0)
        with prvals := pvs })
    rw [toPState_prvals_nl (becomeFollower { s with votes := recordVote s.votes src (!reject) }
      s.term (W64 0)) pvs (by simp [becomeFollower]), toPState_becomeFollower, Hs1]
    exact Step.abandon _ (by rw [toPState_role, Hpre]; decide)
  all_goals
    show Step cfg id (toPState s) []
      (toPState { campaignState id { s with votes := recordVote s.votes src (!reject) } false peers
        with prvals := pvs })
    rw [← Hs1]
    exact step_campaignState cfg id { s with votes := recordVote s.votes src (!reject) } false
      peers pvs Hnl Hin Hnw (Hperm rfl)

omit [GoGlobalContext] [GoSemanticsFunctions] in
/-- Stepping down and then answering a vote request, in one protocol step. -/
theorem step_stepdown_then_vote (id : w64) (s : PState) (m : Msg)
    (Hty : m.ty = .vote) (Hto : m.dst = id) (Hfrom : m.src ≠ W64 0)
    (Hlt : uint.Z s.term < uint.Z m.term)
    (Hutd : plogUpToDate s.base s.log (entryID.mk m.logterm m.index) = true) :
    Step cfg id s ([m] ++ [m])
      (psendMsgs { pbecomeFollower s m.term (W64 0) with vote := m.src }
        [Msg.plain .voteResp id m.src m.term false]) := by
  have Hne : m.term ≠ s.term := by intro Heq; rw [Heq] at Hlt; omega
  have Hh := Step.higherTerm (cfg := cfg) m s Hlt Hto (by rw [Hty]; simp [fromLeader])
  rw [Hty] at Hh
  simp only [fromLeader] at Hh
  refine .trans _ _ _ _ _ Hh ?_
  -- `pbecomeFollower` to a strictly greater term clears the vote and the leader, so
  -- `PCanVote` holds.
  exact Step.grantVote (cfg := cfg) (id := id) m (pbecomeFollower s m.term (W64 0)) Hty Hto
    Hfrom rfl (Or.inr ⟨by simp [pbecomeFollower, Hne], rfl⟩) Hutd

omit [GoGlobalContext] [GoSemanticsFunctions] in
/-- Stepping down and then declining. -/
theorem step_stepdown_then_reject (id : w64) (s : PState) (m : Msg)
    (Hty : m.ty = .vote) (Hto : m.dst = id) (Hlt : uint.Z s.term < uint.Z m.term) :
    Step cfg id s ([m] ++ [m])
      (psendMsgs (pbecomeFollower s m.term (W64 0))
        [Msg.plain .voteResp id m.src m.term true]) := by
  have Hh := Step.higherTerm (cfg := cfg) m s Hlt Hto (by rw [Hty]; simp [fromLeader])
  rw [Hty] at Hh
  simp only [fromLeader] at Hh
  exact .trans _ _ _ _ _ Hh (Step.rejectVote m _ Hty Hto)

omit [GoGlobalContext] [GoSemanticsFunctions] in
/-- Recording a vote response and then winning. -/
theorem step_record_then_win (id : w64) (s : PState) (m : Msg) (mt : GMap w64 w64)
    (ms : List Msg)
    (Hty : m.ty = .voteResp) (Hto : m.dst = id) (Hterm : m.term = s.term)
    (Hrole : s.role = .candidate)
    (Hmt : LeaderMatchOk id { s with votes := recordVote s.votes m.src (!m.reject) } mt)
    (Hms : ∀ m' ∈ ms, ReplOk id
      (pwinState id { s with votes := recordVote s.votes m.src (!m.reject) } mt) m')
    (Hq : IsQuorum cfg (granted (recordVote s.votes m.src (!m.reject))))
    (Hnw : plogLastIndexZ s.base s.log + 1 < 2 ^ 64) :
    Step cfg id s ([m] ++ [])
      (psendMsgs (pwinState id { s with votes := recordVote s.votes m.src (!m.reject) } mt)
        ([pselfAck id (pwinState id { s with votes := recordVote s.votes m.src (!m.reject) } mt)]
          ++ ms)) :=
  .trans _ _ _ _ _ (Step.recordVote m s Hty Hto Hterm Hrole)
    (Step.win _ mt ms Hrole Hq Hnw Hmt Hms)

omit [GoGlobalContext] [GoSemanticsFunctions] in
/-- Recording a vote response and then losing. -/
theorem step_record_then_lose (id : w64) (s : PState) (m : Msg)
    (Hty : m.ty = .voteResp) (Hto : m.dst = id) (Hterm : m.term = s.term)
    (Hrole : s.role = .candidate)
    (Hq : ¬ IsQuorum cfg (cfg \ rejected (recordVote s.votes m.src (!m.reject)))) :
    Step cfg id s ([m] ++ [])
      (pbecomeFollower { s with votes := recordVote s.votes m.src (!m.reject) } s.term (W64 0)) :=
  .trans _ _ _ _ _ (Step.recordVote m s Hty Hto Hterm Hrole) (Step.lose _ Hrole Hq)

end step_lemmas

end EtcdGrove
end Perennial
