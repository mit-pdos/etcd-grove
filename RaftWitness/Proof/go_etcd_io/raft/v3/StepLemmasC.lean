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
/- (2026-10-18, D19b stage 5) the bound of the indices a step may create (`Step`'s) -/
variable {B : Int}

omit [GoGlobalContext] [GoSemanticsFunctions] in
/-- `step_send_frees` at `c`. -/
theorem stepC_send_frees (id : w64) (ps : PState) (ms : List Msg)
    (Hms : ∀ m ∈ ms, (m.ty = .preVote ∨ m.ty = .preVoteResp) ∧ m.src = id) :
    StepC c id B ps [] (psendMsgs ps ms) := by
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

omit [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions] in
/-- The voters a campaign asks (2026-10-20, witness support, W3b-C): every other voter of either
half but the configuration's witness, which `campaign` skips (it is asked by
`sendRequestVoteToWitness` once the candidate is a vote short). Without a witness, every other
voter (`campSet_nw`). -/
def campSet (c : CfgM) (id : w64) : GSet w64 :=
  if c.wit = W64 0 then c.voters \ {[id]} else (c.voters \ {[id]}) \ {[c.wit]}

omit [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions] in
theorem campSet_nw (c : CfgM) (id : w64) (h : c.wit = W64 0) :
    campSet c id = c.voters \ {[id]} := by
  unfold campSet; exact if_pos h

omit [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions] in
theorem campSet_ne {c : CfgM} {id z : w64} (h : z ∈ campSet c id) : z ≠ id := by
  unfold campSet at h
  split at h <;> simp_all [GMap.elem_of_difference, GMap.elem_of_singleton]

omit [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions] in
/-- `campSet` lists as the other voters but the witness, in any order. -/
theorem campSet_perm_filter (c : CfgM) (id : w64) :
    elements (campSet c id) ≡ₚ (elements (c.voters \ {[id]})).filter
      (fun y => decide (c.wit = W64 0 ∨ y ≠ c.wit)) := by
  refine (List.perm_ext_iff_of_nodup (GMap.NoDup_elements _)
    ((GMap.NoDup_elements _).filter _)).2 ?_
  intro z
  rw [List.mem_filter, GMap.elem_of_elements, GMap.elem_of_elements]
  unfold campSet
  by_cases hw : c.wit = W64 0
  · rw [ite_eq_left hw]; simp [hw]
  · rw [ite_eq_right hw]; simp only [hw, GMap.elem_of_difference, GMap.elem_of_singleton, false_or,
      decide_eq_true_eq]

omit [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions] in
/-- What a campaign sends `campSet`, a sub-permutation of what it would send every other voter. -/
theorem campSet_subperm {β : Type _} (c : CfgM) (id : w64) (f : w64 → β) (peers : List w64)
    (h : peers ≡ₚ elements (campSet c id)) :
    (peers.map f).Subperm ((elements (c.voters \ {[id]})).map f) :=
  by
  have hs : ((elements (c.voters \ {[id]})).filter
      (fun y => decide (c.wit = W64 0 ∨ y ≠ c.wit))).Sublist (elements (c.voters \ {[id]})) := by
    apply List.filter_sublist
  exact ((h.trans (campSet_perm_filter c id)).map f).subperm.trans (hs.map f).subperm

/-- `step_campaignState` at `c`: a campaign by a voter of either half, asking every other
voter of either half (2026-10-20: but the witness, `campSet`; the protocol's `campaign` asks
every one, then the witness's request is dropped, `drain`). -/
theorem stepC_campaignState (id : w64) (s : NState) (pre : Bool) (peers : List w64)
    (pvs : GMap w64 Progress) (Hnl : s.role ≠ .leader) (Hin : id ∈ c.voters)
    (Hnw : uint.Z s.term + 1 < 2 ^ 64) (Hperm : peers ≡ₚ elements (campSet c id))
    (cl : List w8 := []) :
    StepC c id B (toPState s) [] (toPState { campaignState id s pre peers cl with prvals := pvs }) := by
  have Hrole : (campaignState id s pre peers cl).role ≠ .leader := by
    cases pre <;> simp [campaignState, sendMsgs, becomePrecandidate, becomeCandidate]
  rw [toPState_prvals_nl (campaignState id s pre peers cl) pvs Hrole]
  cases pre
  · show StepC c id B (toPState s) [] (toPState (sendMsgs (becomeCandidate id s) _))
    rw [toPState_sendMsgs, toPState_becomeCandidate]
    exact StepC.trans _ [] _ [] _
      (StepC.campaign (toPState s) (elements (c.voters \ {[id]})) cl
        (by rw [toPState_role]; exact proleRole_not_leader _ Hnl) Hin Hnw (List.Perm.refl _))
      (StepC.drain _ _ ((List.subperm_append_left _).2
        ((List.subperm_append_left _).2 (campSet_subperm c id _ peers Hperm))))
  · show StepC c id B (toPState s) [] (toPState (sendMsgs (becomePrecandidate s) _))
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
    (Hperm : won = true → peers ≡ₚ elements (campSet c id)) :
    StepC c id B (toPState s) []
      (toPState { prevoteRespResult id s src reject won lost peers with prvals := pvs }) := by
  have Hs1 : toPState { s with votes := recordVote s.votes src (!reject) } = toPState s :=
    toPState_votes_pre _ _ Hpre
  have Hnl : s.role ≠ .leader := by rw [Hpre]; decide
  cases won <;> cases lost
  · show StepC c id B (toPState s) []
      (toPState { { s with votes := recordVote s.votes src (!reject) } with prvals := pvs })
    rw [toPState_prvals_nl { s with votes := recordVote s.votes src (!reject) } pvs Hnl, Hs1]
    exact .refl _
  · show StepC c id B (toPState s) []
      (toPState { becomeFollower { s with votes := recordVote s.votes src (!reject) } s.term (W64 0)
        with prvals := pvs })
    rw [toPState_prvals_nl (becomeFollower { s with votes := recordVote s.votes src (!reject) }
      s.term (W64 0)) pvs (by simp [becomeFollower]), toPState_becomeFollower, Hs1]
    exact StepC.abandon _ (by rw [toPState_role, Hpre]; decide)
  all_goals
    show StepC c id B (toPState s) []
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
    (Hnw : plogLastIndexZ s.base s.log + 1 ≤ B)
    (Hsn : ∀ m' ∈ ms, m'.ty = .snap → m'.dst ∈ c.voters ∪ c.learners) :
    StepC c id B s ([m] ++ [])
      (psendMsgs (pwinState id { s with votes := recordVote s.votes m.src (!m.reject) } mt)
        ([pselfAck id (pwinState id { s with votes := recordVote s.votes m.src (!m.reject) } mt)]
          ++ ms)) :=
  .trans _ _ _ _ _ (StepC.recordVote m s Hty Hto Hterm Hrole)
    (StepC.win _ mt ms Hrole Hq Hnw Hmt Hms Hsn)

omit [GoGlobalContext] [GoSemanticsFunctions] in
/-- Recording a vote response and then losing, at `c`. -/
theorem stepC_record_then_lose (id : w64) (s : PState) (m : Msg)
    (Hty : m.ty = .voteResp) (Hto : m.dst = id) (Hterm : m.term = s.term)
    (Hrole : s.role = .candidate)
    (Hq : JLost c (recordVote s.votes m.src (!m.reject))) :
    StepC c id B s ([m] ++ [])
      (pbecomeFollower { s with votes := recordVote s.votes m.src (!m.reject) } s.term (W64 0)) :=
  .trans _ _ _ _ _ (StepC.recordVote m s Hty Hto Hterm Hrole) (StepC.lose _ Hrole Hq)

omit [GoGlobalContext] [GoSemanticsFunctions] in
/-- Dropping a message, at `c`. -/
theorem stepC_drop (id : w64) (s : PState) : StepC c id B s [] s := .refl s

omit [GoGlobalContext] [GoSemanticsFunctions] in
/-- Stepping down and then answering a vote request, at `c`. -/
theorem stepC_stepdown_then_vote (id : w64) (s : PState) (m : Msg)
    (Hty : m.ty = .vote) (Hto : m.dst = id) (Hfrom : m.src ≠ W64 0)
    (Hlt : uint.Z s.term < uint.Z m.term)
    (Hutd : plogUpToDate s.base s.log (entryID.mk m.logterm m.index) = true) :
    StepC c id B s ([m] ++ [m])
      (psendMsgs { pbecomeFollower s m.term (W64 0) with vote := m.src }
        [Msg.plain .voteResp id m.src m.term false]) := by
  have Hne : m.term ≠ s.term := by intro Heq; rw [Heq] at Hlt; omega
  have Hh := StepC.higherTerm (c := c) (B := B) m s Hlt Hto (by rw [Hty]; simp [fromLeader])
  rw [Hty] at Hh
  simp only [fromLeader] at Hh
  refine .trans _ _ _ _ _ Hh ?_
  exact StepC.grantVote (c := c) (id := id) m (pbecomeFollower s m.term (W64 0)) Hty Hto
    Hfrom rfl (Or.inr ⟨by simp [pbecomeFollower, Hne], rfl⟩) Hutd

omit [GoGlobalContext] [GoSemanticsFunctions] in
/-- Stepping down and then declining, at `c`. -/
theorem stepC_stepdown_then_reject (id : w64) (s : PState) (m : Msg)
    (Hty : m.ty = .vote) (Hto : m.dst = id) (Hlt : uint.Z s.term < uint.Z m.term) :
    StepC c id B s ([m] ++ [m])
      (psendMsgs (pbecomeFollower s m.term (W64 0))
        [Msg.plain .voteResp id m.src m.term true]) := by
  have Hh := StepC.higherTerm (c := c) (B := B) m s Hlt Hto (by rw [Hty]; simp [fromLeader])
  rw [Hty] at Hh
  simp only [fromLeader] at Hh
  exact .trans _ _ _ _ _ Hh (StepC.rejectVote m _ Hty Hto)

end step_lemmasC

end EtcdGrove
end Perennial
