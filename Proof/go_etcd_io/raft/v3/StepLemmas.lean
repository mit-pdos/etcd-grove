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
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]
-- The (fixed) set of voters.
variable (cfg : GSet w64)
/- (2026-10-18, D19b stage 5) the bound of the indices a step may create (`Step`'s) -/
variable {B : Int}

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

end step_lemmas

end EtcdGrove
end Perennial
