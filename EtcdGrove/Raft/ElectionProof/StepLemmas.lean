/-
Port of `election_proof/step_lemmas.v`: pure model-level lemmas and vocabulary.
-/
import EtcdGrove.Raft.ElectionProof.Defs

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
`bcastAppend` put on the network; it is irrelevant unless `won`.

`ms` is an arbitrary list of `App`s rather than one per peer, matching `Step.win` —
see the comment there for why the exact broadcast is not pinned down. -/
def voteRespResult (id : w64) (s : NState) (src : w64) (reject won lost : Bool)
    (ms : List Msg) : NState :=
  let s1 := { s with votes := recordVote s.votes src (!reject) }
  if won then sendMsgs (becomeLeader id s1) ms
  else if lost then becomeFollower s1 s1.term (W64 0)
  else s1

/-- An election message: the only ones in scope. -/
def ElectionMsg (m : raftpb.Message) : Prop :=
  m.Type' = MsgHup ∨ m.Type' = MsgVote ∨ m.Type' = MsgVoteResp

/-! ## Model-level lemmas justifying each branch of `Step`

Protocol facts, about `PState`: the `Step` proof applies them to `toPState s`. -/

/-- The protocol reading of `voteRespResult`. -/
def pvoteRespResult (id : w64) (ps : PState) (src : w64) (reject won lost : Bool)
    (ms : List Msg) : PState :=
  let s1 := { ps with votes := recordVote ps.votes src (!reject) }
  if won then psendMsgs (pbecomeLeader id s1) ms
  else if lost then pbecomeFollower s1 s1.term (W64 0)
  else s1

theorem toPState_voteRespResult (id : w64) (s : NState) (src : w64) (reject won lost : Bool)
    (ms : List Msg) :
    toPState (voteRespResult id s src reject won lost ms) =
      pvoteRespResult id (toPState s) src reject won lost ms := by
  unfold voteRespResult pvoteRespResult
  cases won <;> cases lost <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · rfl
  · exact toPState_becomeFollower _ _ _
  · rw [toPState_sendMsgs, toPState_becomeLeader]; rfl
  · rw [toPState_sendMsgs, toPState_becomeLeader]; rfl

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

/-! ## Branch lemmas

These are pure facts about the protocol, independent of the program logic; the WP
proofs feed them to `ownRaftGhost_step`. -/

/-- Dropping a message is always legal. -/
theorem step_drop (id : w64) (s : PState) : Step cfg id s [] s := .refl s

/-- Stepping down and then answering a vote request, in one protocol step. -/
theorem step_stepdown_then_vote (id : w64) (s : PState) (m : Msg)
    (Hty : m.ty = .vote) (Hto : m.dst = id) (Hfrom : m.src ≠ W64 0)
    (Hlt : uint.Z s.term < uint.Z m.term) :
    Step cfg id s ([m] ++ [m])
      (psendMsgs { pbecomeFollower s m.term (W64 0) with vote := m.src }
        [⟨.voteResp, id, m.src, m.term, false⟩]) := by
  have Hne : m.term ≠ s.term := by intro Heq; rw [Heq] at Hlt; omega
  have Hh := Step.higherTerm (cfg := cfg) m s Hlt Hto
  rw [Hty] at Hh
  simp only [fromLeader] at Hh
  refine .trans _ _ _ _ _ Hh ?_
  have := Step.grantVote (cfg := cfg) (id := id) m (pbecomeFollower s m.term (W64 0)) Hty Hto Hfrom
    rfl (Or.inr ⟨by simp [pbecomeFollower, Hne], rfl⟩)
  exact this

/-- Stepping down and then declining. -/
theorem step_stepdown_then_reject (id : w64) (s : PState) (m : Msg)
    (Hty : m.ty = .vote) (Hto : m.dst = id) (Hlt : uint.Z s.term < uint.Z m.term) :
    Step cfg id s ([m] ++ [m])
      (psendMsgs (pbecomeFollower s m.term (W64 0)) [⟨.voteResp, id, m.src, m.term, true⟩]) := by
  have Hh := Step.higherTerm (cfg := cfg) m s Hlt Hto
  rw [Hty] at Hh
  simp only [fromLeader] at Hh
  exact .trans _ _ _ _ _ Hh (Step.rejectVote m _ Hty Hto)

/-- Recording a vote response and then winning. -/
theorem step_record_then_win (id : w64) (s : PState) (m : Msg) (ms : List Msg)
    (Hty : m.ty = .voteResp) (Hto : m.dst = id) (Hterm : m.term = s.term)
    (Hrole : s.role = .candidate)
    (Hms : AppSends id s.term ms)
    (Hq : IsQuorum cfg (granted (recordVote s.votes m.src (!m.reject)))) :
    Step cfg id s ([m] ++ [])
      (psendMsgs (pbecomeLeader id { s with votes := recordVote s.votes m.src (!m.reject) }) ms) :=
  .trans _ _ _ _ _ (Step.recordVote m s Hty Hto Hterm Hrole) (Step.win _ ms Hrole Hq Hms)

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
