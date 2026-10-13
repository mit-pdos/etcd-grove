/-
`StepLemmas.lean`'s branch lemmas at a joint configuration (2026-10-13, reconfiguration stage
A2), Lean-first: the same statements with `StepC c` for `Step cfg`, the voters of either half
(`c.voters`) for `cfg`, `JQuorum`/`JLost` for the quorum tests. Pure.
-/
module

public import Proof.go_etcd_io.raft.v3.StepLemmas
public import Proof.go_etcd_io.raft.v3.Protocol.StepC

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

section step_lemmasC
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]
variable (c : CfgM)

omit [GoGlobalContext] [GoSemanticsFunctions] in
/-- `step_send_frees` at `c`. -/
theorem stepC_send_frees (id : w64) (ps : PState) (ms : List Msg)
    (Hms : ∀ m ∈ ms, (m.ty = .preVote ∨ m.ty = .preVoteResp) ∧ m.src = id) :
    StepC c id ps [] (psendMsgs ps ms) := by
  induction ms generalizing ps with
  | nil =>
    have : psendMsgs ps [] = ps := by simp [psendMsgs]
    rw [this]; exact .refl ps
  | cons m ms IH =>
    have Hm := Hms m (List.mem_cons_self ..)
    have Heq : psendMsgs ps (m :: ms) = psendMsgs (psendMsgs ps [m]) ms := by
      simp [psendMsgs]
    rw [Heq]
    have := StepC.trans _ [] _ [] _ (StepC.sendFree (c := c) ps m Hm.1 Hm.2)
      (IH (psendMsgs ps [m]) (fun m' h => Hms m' (List.mem_cons_of_mem _ h)))
    simpa using this

/-- `step_campaignState` at `c`: a campaign by a voter of either half, asking every other
voter of either half. -/
theorem stepC_campaignState (id : w64) (s : NState) (pre : Bool) (peers : List w64)
    (pvs : GMap w64 Progress) (Hnl : s.role ≠ .leader) (Hin : id ∈ c.voters)
    (Hnw : uint.Z s.term + 1 < 2 ^ 64) (Hperm : peers ≡ₚ elements (c.voters \ {[id]}))
    (cl : List w8 := []) :
    StepC c id (toPState s) [] (toPState { campaignState id s pre peers cl with prvals := pvs }) := by
  have Hrole : (campaignState id s pre peers cl).role ≠ .leader := by
    cases pre <;> simp [campaignState, sendMsgs, becomePrecandidate, becomeCandidate]
  rw [toPState_prvals_nl (campaignState id s pre peers cl) pvs Hrole]
  cases pre
  · show StepC c id (toPState s) [] (toPState (sendMsgs (becomeCandidate id s) _))
    rw [toPState_sendMsgs, toPState_becomeCandidate]
    exact StepC.campaign (toPState s) peers cl (by rw [toPState_role]; exact proleRole_not_leader _ Hnl)
      Hin Hnw Hperm
  · show StepC c id (toPState s) [] (toPState (sendMsgs (becomePrecandidate s) _))
    rw [toPState_sendMsgs, toPState_becomePrecandidate]
    refine StepC.trans _ [] _ [] _
      (StepC.abandon (c := c) (id := id) (toPState s)
        (by rw [toPState_role]; exact proleRole_not_leader _ Hnl))
      (stepC_send_frees c id _ _ ?_)
    intro m Hm
    rcases List.mem_append.1 Hm with h | h
    · simp only [List.mem_singleton] at h; subst h; exact ⟨Or.inr rfl, rfl⟩
    · simp only [List.mem_map] at h
      obtain ⟨_, _, rfl⟩ := h
      exact ⟨Or.inl rfl, rfl⟩

/-- `step_prevoteRespResult` at `c`. -/
theorem stepC_prevoteRespResult (id : w64) (s : NState) (src : w64) (reject won lost : Bool)
    (peers : List w64) (pvs : GMap w64 Progress) (Hpre : s.role = .preCandidate)
    (Hin : id ∈ c.voters) (Hnw : uint.Z s.term + 1 < 2 ^ 64)
    (Hperm : won = true → peers ≡ₚ elements (c.voters \ {[id]})) :
    StepC c id (toPState s) []
      (toPState { prevoteRespResult id s src reject won lost peers with prvals := pvs }) := by
  have Hs1 : toPState { s with votes := recordVote s.votes src (!reject) } = toPState s :=
    toPState_votes_pre _ _ Hpre
  have Hnl : s.role ≠ .leader := by rw [Hpre]; decide
  cases won <;> cases lost
  · show StepC c id (toPState s) []
      (toPState { { s with votes := recordVote s.votes src (!reject) } with prvals := pvs })
    rw [toPState_prvals_nl { s with votes := recordVote s.votes src (!reject) } pvs Hnl, Hs1]
    exact .refl _
  · show StepC c id (toPState s) []
      (toPState { becomeFollower { s with votes := recordVote s.votes src (!reject) } s.term (W64 0)
        with prvals := pvs })
    rw [toPState_prvals_nl (becomeFollower { s with votes := recordVote s.votes src (!reject) }
      s.term (W64 0)) pvs (by simp [becomeFollower]), toPState_becomeFollower, Hs1]
    exact StepC.abandon _ (by rw [toPState_role, Hpre]; decide)
  all_goals
    show StepC c id (toPState s) []
      (toPState { campaignState id { s with votes := recordVote s.votes src (!reject) } false peers
        with prvals := pvs })
    rw [← Hs1]
    exact stepC_campaignState c id { s with votes := recordVote s.votes src (!reject) } false
      peers pvs Hnl Hin Hnw (Hperm rfl)

omit [GoGlobalContext] [GoSemanticsFunctions] in
/-- Recording a vote response and then winning, at `c`. -/
theorem stepC_record_then_win (id : w64) (s : PState) (m : Msg) (mt : GMap w64 w64)
    (ms : List Msg)
    (Hty : m.ty = .voteResp) (Hto : m.dst = id) (Hterm : m.term = s.term)
    (Hrole : s.role = .candidate)
    (Hmt : LeaderMatchOk id { s with votes := recordVote s.votes m.src (!m.reject) } mt)
    (Hms : ∀ m' ∈ ms, ReplOk id
      (pwinState id { s with votes := recordVote s.votes m.src (!m.reject) } mt) m')
    (Hq : JQuorum c (granted (recordVote s.votes m.src (!m.reject))))
    (Hnw : plogLastIndexZ s.base s.log + 1 < 2 ^ 64) :
    StepC c id s ([m] ++ [])
      (psendMsgs (pwinState id { s with votes := recordVote s.votes m.src (!m.reject) } mt)
        ([pselfAck id (pwinState id { s with votes := recordVote s.votes m.src (!m.reject) } mt)]
          ++ ms)) :=
  .trans _ _ _ _ _ (StepC.recordVote m s Hty Hto Hterm Hrole)
    (StepC.win _ mt ms Hrole Hq Hnw Hmt Hms)

omit [GoGlobalContext] [GoSemanticsFunctions] in
/-- Recording a vote response and then losing, at `c`. -/
theorem stepC_record_then_lose (id : w64) (s : PState) (m : Msg)
    (Hty : m.ty = .voteResp) (Hto : m.dst = id) (Hterm : m.term = s.term)
    (Hrole : s.role = .candidate)
    (Hq : JLost c (recordVote s.votes m.src (!m.reject))) :
    StepC c id s ([m] ++ [])
      (pbecomeFollower { s with votes := recordVote s.votes m.src (!m.reject) } s.term (W64 0)) :=
  .trans _ _ _ _ _ (StepC.recordVote m s Hty Hto Hterm Hrole) (StepC.lose _ Hrole Hq)

end step_lemmasC

end EtcdGrove
end Perennial
