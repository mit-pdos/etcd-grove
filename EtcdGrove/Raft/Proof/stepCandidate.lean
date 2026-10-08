/-
Port of election_proof/proof_stepCandidate.v.
-/
import EtcdGrove.Raft.Spec.stepCandidate
import EtcdGrove.Raft.Spec.raft__poll
import EtcdGrove.Raft.Spec.raft__becomeLeader
import EtcdGrove.Raft.Spec.raft__becomeFollower
import EtcdGrove.Raft.Spec.raft__bcastAppend
import EtcdGrove.Raft.Spec.raft__handleAppendEntries
import EtcdGrove.Raft.Spec.raft__handleHeartbeat
import EtcdGrove.Raft.Spec.raft__handleSnapshot
import EtcdGrove.Raft.Spec.raft__campaign

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
/-- By type. `MsgProp`: `Infof`, then `return ErrProposalDropped` (the global's
points-to from `isInitialized_access`). `MsgApp`: `becomeFollower(m.Term, m.From)` with
`m.Term = s.term`, then `handleAppendEntries` at the follower state. `MsgHeartbeat`: the
same `becomeFollower`, then `handleHeartbeat`. `MsgBeat`, `MsgAppResp`,
`MsgHeartbeatResp`: no arm.

`MsgVoteResp`, unchanged since 2026-09: the type switch is walked to the
`myVoteRespType` arm (`m.Type = MsgVoteResp`, and `state = StateCandidate` so
`myVoteRespType` is `MsgVoteResp` and not `MsgPreVoteResp`), then `poll` records the
vote and the `res` switch does one of three things: win and broadcast, lose and step
down, or nothing.

Each arm lands on `voteRespResult` directly. `VoteWon` is `becomeLeader` followed by
`bcastAppend`, whose spec gives *some* `ReplSends` list rather than one `App` per peer
-- which is what `Step.win` asks for. `VoteLost` is `becomeFollower(r.Term, None)`, and
`becomeFollower s1 s1.term (W64 0)` is verbatim `voteRespResult`'s `lost` branch.
`VotePending` leaves the state at `s1` and sends nothing. -/
theorem stepCandidate.wp_proof
    (wp_raft_poll : raft.poll.spec (GF := GF) (hG := hG))
    (wp_raft_becomeLeader : raft.becomeLeader.spec (GF := GF) (hG := hG))
    (wp_raft_becomeFollower : raft.becomeFollower.spec (GF := GF) (hG := hG))
    (wp_raft_bcastAppend : raft.bcastAppend.spec (GF := GF) (hG := hG))
    (wp_raft_handleAppendEntries : raft.handleAppendEntries.spec (GF := GF) (hG := hG))
    (wp_raft_handleHeartbeat : raft.handleHeartbeat.spec (GF := GF) (hG := hG))
    (wp_raft_handleSnapshot : raft.handleSnapshot.spec (GF := GF) (hG := hG))
    (wp_raft_campaign : raft.campaign.spec (GF := GF) (hG := hG)) :
    stepCandidate.spec (GF := GF) (hG := hG) := by
  intro cfg r id s m ents sv voters Hty Hterm Hrole Hcfg Happ Hhb Hpvnw
  wp_start as H
  iNamed H
  ihave #Hinit := isInitialized_access $$ Hpkg
  unfold isInitialized
  icases Hinit with ⟨%e1, %e2, %e3, %e4, %errPropDropped, %gr, #Hinit⟩
  iNamed Hinit
  wp_alloc m_ptr as m; wp_pures; wp_alloc r_ptr as r; wp_pures
  wp_alloc myVoteRespType_ptr as myVoteRespType; wp_pures; wp_load; wp_pures
  -- `myVoteRespType`: `MsgPreVoteResp` for a pre-candidate, `MsgVoteResp` for a
  -- candidate; the two arms are joined
  wp_apply raft.wp_load_state $$ Hphys as Hphys
  wp_pures
  have Hpre_iff : stateW64 s.role = W64 3 ↔ s.role = .preCandidate := by
    cases s.role <;> decide
  -- TODO(no-wp-auto): wp_join runs (cont first, then the cases): wp_pures; wp_load; wp_pures | ∅ | ∅
  wp_join iprop(myVoteRespType_ptr ↦
      (if s.role = .preCandidate then W32 18 else W32 6))
    with [myVoteRespType] as myVoteRespType
  · rw [show raftpb.MsgPreVoteResp = #(W32 18) from rfl]
    wp_store; wp_pures
    rw [if_pos (Hpre_iff.1 Hif)]
    iframe myVoteRespType
    ipureintro; exact rfl
  · rw [show raftpb.MsgVoteResp = #(W32 6) from rfl]
    wp_store; wp_pures
    rw [if_neg (fun h => Hif (Hpre_iff.2 h))]
    iframe myVoteRespType
    ipureintro; exact rfl
  -- kept opaque below, so that the arms' `decide` rewrites find the program's
  -- comparisons and not this one
  generalize Hmvr : (if s.role = .preCandidate then W32 18 else W32 6) = mvr
  have Hmp : s.role = .preCandidate → mvr = W32 18 := by
    intro Hp; rw [← Hmvr, if_pos Hp]
  have Hmc : s.role ≠ .preCandidate → mvr = W32 6 := by
    intro Hp; rw [← Hmvr, if_neg Hp]
  clear Hmvr
  rcases Hty with Hty | Hty | Hty | Hty | Hty | Hty | Hty
  · -- `MsgVoteResp`: none of `MsgProp`, `MsgApp`, `MsgHeartbeat`, `MsgSnap`, so it falls
    -- through to `myVoteRespType`
    have Hterm' := Hterm (Or.inl Hty)
    rw [Hty]
    simp only [MsgVoteResp]
    wp_pures; wp_load; wp_pures; iclear myVoteRespType
    rcases Hrole with Hrole | Hrole
    rotate_left
    · -- a pre-candidate: `myVoteRespType` is `MsgPreVoteResp`; a vote response is
      -- ignored
      rw [Hmp Hrole]
      wp_pures; iclear m r
      iapply HΦ $$ %GoInterface.nil %s %false
      iframe Hphys
      simp only [Bool.false_eq_true, ↓reduceIte]
      ipureintro
      refine ⟨?_, trivial⟩
      simp [CandidateStepResult, Hty, Hrole, MsgVoteResp]
    rw [Hmc (by rw [Hrole]; decide)]
    wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures
    have Hcfg_ne : cfg ≠ ∅ := fun h => GMap.not_elem_of_empty id (h ▸ Hcfg)
    wp_apply wp_raft_poll _ _ _ _ _ _ _ Hcfg_ne $$ [$Hphys]
      as %g %rj0 %res ⟨Hphys, %Hres, %Hwon, %Hlost⟩
    wp_pures; wp_alloc res_ptr as res; wp_pures; wp_alloc rj_ptr as rj; wp_pures
    wp_alloc gr_ptr as gr; wp_pures; wp_store; wp_pures; wp_store; wp_pures; wp_store; wp_pures
    wp_load; wp_pures
    -- the `Infof` that follows reads `r.id`, `r.Term` and `r.logger`
    wp_apply raft.wp_load_id $$ Hphys as Hphys
    wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures; iclear m gr rj
    -- TODO(no-wp-auto): macro `wp_raft_log` runs wp_auto: wp_pures | wp_pures; wp_load; wp_pures | wp_pures | wp_pures; wp_load; wp_pures; iclear res | ∅
    wp_raft_log
    rcases Hres with rfl | rfl | rfl
    · -- `quorum.VoteWon`: become leader and broadcast. `poll` does not touch the role,
      -- so we are still a candidate: not a pre-candidate, so this is `becomeLeader` and
      -- not `campaign`.
      simp only [VoteWon]
      wp_pures; wp_load; wp_pures
      wp_apply raft.wp_load_state $$ Hphys as Hphys
      wp_pures
      rw [decide_eq_false (by simp only [Hrole]; decide)]
      wp_pures; wp_load; wp_pures
      wp_apply wp_raft_becomeLeader _ _ _ _ (by simp only [Hrole]; decide) Hcfg $$ [$Hphys]
        as %pvs1 ⟨Hphys, %Hmb⟩
      wp_pures; wp_load; wp_pures; iclear r
      -- `bcastAppend` adds *some* list of `App`s from `id` at the current term -- not one
      -- per peer; see `Spec/raft__bcastAppend.lean`.
      wp_apply wp_raft_bcastAppend $$ [$Hphys] as %ms %pvs ⟨Hphys, %Hms, %Hmm⟩
      wp_pures
      iapply HΦ $$ %GoInterface.nil %_ %false
      iframe Hphys
      simp only [Bool.false_eq_true, ↓reduceIte]
      ipureintro
      refine ⟨?_, trivial⟩
      simp only [CandidateStepResult, Hty, Hrole, ↓reduceIte]
      refine ⟨trivial, ?_⟩
      have Hnp : ¬ (PRole.candidate = PRole.preCandidate) := by decide
      simp only [Hnp, ↓reduceIte]
      refine ⟨true, false, ms, pvs, fun _ => ⟨Hwon rfl, ?_, ?_⟩, fun h => absurd h (by decide), ?_⟩
      · exact (replSends_prvals _ _ pvs1 ms).1 Hms
      · rw [Hmm]; exact Hmb
      · cases s; rfl
    · -- `quorum.VoteLost`: step down at the unchanged term
      simp only [VoteLost]
      wp_pures; wp_load; wp_pures
      -- the `r.Term` the code passes is `s1`'s term
      wp_apply raft.wp_load_Term $$ Hphys as Hphys
      wp_pures; wp_load; wp_pures; iclear r
      wp_apply wp_raft_becomeFollower $$ [$Hphys] as %pvs Hphys
      wp_pures
      iapply HΦ $$ %GoInterface.nil %_ %false
      iframe Hphys
      simp only [Bool.false_eq_true, ↓reduceIte]
      ipureintro
      refine ⟨?_, trivial⟩
      simp only [CandidateStepResult, Hty, Hrole, ↓reduceIte]
      refine ⟨trivial, ?_⟩
      have Hnp : ¬ (PRole.candidate = PRole.preCandidate) := by decide
      simp only [Hnp, ↓reduceIte]
      refine ⟨false, true, [], pvs, fun h => absurd h (by decide), fun _ => Hlost rfl, ?_⟩
      cases s; rfl
    · -- `quorum.VotePending`: neither switch arm fires; keep waiting
      simp only [VotePending]
      wp_pures; iclear r
      iapply HΦ $$ %GoInterface.nil %_ %false
      iframe Hphys
      simp only [Bool.false_eq_true, ↓reduceIte]
      ipureintro
      refine ⟨?_, trivial⟩
      simp only [CandidateStepResult, Hty, Hrole, ↓reduceIte]
      refine ⟨trivial, ?_⟩
      have Hnp : ¬ (PRole.candidate = PRole.preCandidate) := by decide
      simp only [Hnp, ↓reduceIte]
      -- nothing wrote a `Progress`: the values are `s1`'s own
      refine ⟨false, false, [], s.prvals, fun h => absurd h (by decide),
        fun h => absurd h (by decide), ?_⟩
      cases s; simp only at Hrole; subst Hrole; rfl
  · -- `MsgProp`: no leader to forward to; dropped
    rw [Hty]
    simp only [MsgProp]
    wp_pures; wp_load; wp_pures; iclear m myVoteRespType
    wp_apply raft.wp_load_id $$ Hphys as Hphys
    wp_pures; wp_load; wp_pures
    wp_apply raft.wp_load_Term $$ Hphys as Hphys
    wp_pures
    -- TODO(no-wp-auto): macro `wp_raft_log` runs wp_auto: wp_pures | wp_pures; wp_load; wp_pures; iclear r | wp_pures | wp_pures; wp_load; wp_pures | ∅
    wp_raft_log
    iapply HΦ $$ %errPropDropped %s %true
    iframe Hphys
    simp only [↓reduceIte]
    isplitr
    · ipureintro
      simp [CandidateStepResult, Hty, MsgVoteResp, MsgProp]
    iexact ErrPropDropped
  · -- `MsgApp`: `becomeFollower(m.Term, m.From)`, then `handleAppendEntries`
    obtain ⟨Hwf, Hnw, Hnorm, Hconf⟩ := Happ Hty
    have Hterm' := Hterm (Or.inr (Or.inl Hty))
    rw [Hty]
    simp only [MsgApp]
    wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures; iclear myVoteRespType
    wp_apply wp_raft_becomeFollower $$ [$Hphys] as %pvs Hphys
    wp_pures; wp_load; wp_pures; wp_load; wp_pures; iclear m r
    ihave Hes := Hents $$ %trivial
    icases Hes with ⟨#Hes, Hcap⟩
    wp_apply wp_raft_handleAppendEntries _ _ _ { becomeFollower s m.Term' m.From' with prvals := pvs } _ _ Hwf Hnw Hnorm Hconf $$ [$Hphys $Hes $Hcap]
      as %s' ⟨Hphys, %Hres⟩
    wp_pures
    iapply HΦ $$ %GoInterface.nil %s' %false
    iframe Hphys
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro
    refine ⟨?_, trivial⟩
    simp only [CandidateStepResult, Hty, MsgVoteResp, MsgProp, MsgApp]
    refine ⟨trivial, pvs, ?_⟩
    rw [← Hterm']
    exact Hres
  · -- `MsgHeartbeat`: `becomeFollower(m.Term, m.From)`, then `handleHeartbeat`
    obtain ⟨Hcommit, Hfrom⟩ := Hhb Hty
    have Hterm' := Hterm (Or.inr (Or.inr (Or.inl Hty)))
    rw [Hty]
    simp only [MsgHeartbeat]
    wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures; iclear myVoteRespType
    wp_apply wp_raft_becomeFollower $$ [$Hphys] as %pvs Hphys
    wp_pures; wp_load; wp_pures; wp_load; wp_pures; iclear m r
    wp_apply wp_raft_handleHeartbeat _ _ _ { becomeFollower s m.Term' m.From' with prvals := pvs } _ Hcommit Hfrom $$ [$Hphys] as Hphys
    wp_pures
    iapply HΦ $$ %GoInterface.nil %_ %false
    iframe Hphys
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro
    refine ⟨?_, trivial⟩
    simp only [CandidateStepResult, Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat]
    refine ⟨trivial, pvs, ?_⟩
    rw [← Hterm']
  · -- `MsgBeat`, `MsgAppResp`, `MsgHeartbeatResp`: no arm; `myVoteRespType` is one of
    -- the two response types, neither of these
    rcases Hty with Hty' | Hty' | Hty' <;> rw [Hty'] <;>
      simp only [MsgBeat, MsgAppResp, MsgHeartbeatResp] <;> (wp_pures; wp_load; wp_pures; iclear myVoteRespType)
    all_goals
      by_cases Hp : s.role = .preCandidate
      · rw [Hmp Hp]
        wp_pures; iclear m r
        iapply HΦ $$ %GoInterface.nil %s %false
        iframe Hphys
        simp only [Bool.false_eq_true, ↓reduceIte]
        ipureintro
        refine ⟨?_, trivial⟩
        simp [CandidateStepResult, Hty', MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
          MsgAppResp, MsgHeartbeatResp]
      · rw [Hmc Hp]
        wp_pures; iclear m r
        iapply HΦ $$ %GoInterface.nil %s %false
        iframe Hphys
        simp only [Bool.false_eq_true, ↓reduceIte]
        ipureintro
        refine ⟨?_, trivial⟩
        simp [CandidateStepResult, Hty', MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
          MsgAppResp, MsgHeartbeatResp]
  · -- `MsgSnap`: `becomeFollower(m.Term, m.From)`, then `handleSnapshot`
    have Hterm' := Hterm (Or.inr (Or.inr (Or.inr Hty)))
    rw [Hty]
    ihave Hs := Hsnap $$ %rfl
    icases Hs with ⟨%Hscope, #Hsv, #Hvs⟩
    simp only [MsgSnap]
    wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures; iclear myVoteRespType
    wp_apply wp_raft_becomeFollower $$ [$Hphys] as %pvs Hphys
    wp_pures; wp_load; wp_pures; wp_load; wp_pures; iclear m r
    wp_apply wp_raft_handleSnapshot _ _ _ { becomeFollower s m.Term' m.From' with prvals := pvs }
        _ sv voters rfl rfl Hcfg Hscope $$ [$Hphys $Hsv $Hvs]
      as %s' ⟨Hphys, %Hres⟩
    wp_pures
    iapply HΦ $$ %GoInterface.nil %s' %false
    iframe Hphys
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro
    refine ⟨?_, trivial⟩
    simp only [CandidateStepResult, Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
      MsgAppResp, MsgHeartbeatResp, MsgSnap]
    refine ⟨trivial, pvs, ?_⟩
    rw [← Hterm']
    exact Hres
  · -- `MsgPreVoteResp` (2026-10-04)
    rw [Hty]
    simp only [MsgPreVoteResp]
    wp_pures; wp_load; wp_pures; iclear myVoteRespType
    rcases Hrole with Hrole | Hrole
    · -- a candidate: `myVoteRespType` is `MsgVoteResp`; a stale pre-vote response,
      -- ignored
      rw [Hmc (by rw [Hrole]; decide)]
      wp_pures; iclear m r
      iapply HΦ $$ %GoInterface.nil %s %false
      iframe Hphys
      simp only [Bool.false_eq_true, ↓reduceIte]
      ipureintro
      refine ⟨?_, trivial⟩
      simp [CandidateStepResult, Hty, Hrole, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat,
        MsgBeat, MsgAppResp, MsgHeartbeatResp, MsgSnap, MsgPreVoteResp]
    · -- a pre-candidate: `poll`, then win, lose or wait
      rw [Hmp Hrole]
      wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures
      have Hcfg_ne : cfg ≠ ∅ := fun h => GMap.not_elem_of_empty id (h ▸ Hcfg)
      wp_apply wp_raft_poll _ _ _ _ _ _ _ Hcfg_ne $$ [$Hphys]
        as %g %rj0 %res ⟨Hphys, %Hres, %Hwon, %Hlost⟩
      wp_pures; wp_alloc res_ptr as res; wp_pures; wp_alloc rj_ptr as rj; wp_pures
      wp_alloc gr_ptr as gr; wp_pures; wp_store; wp_pures; wp_store; wp_pures; wp_store; wp_pures
      wp_load; wp_pures
      wp_apply raft.wp_load_id $$ Hphys as Hphys
      wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures; iclear m gr rj
      -- TODO(no-wp-auto): macro `wp_raft_log` runs wp_auto: wp_pures | wp_pures; wp_load; wp_pures | wp_pures | wp_pures; wp_load; wp_pures; iclear res | ∅
      wp_raft_log
      have Hres_pv : ∀ (s' : NState) (won lost : Bool) (peers : List w64)
          (pvs : GMap w64 Progress),
          (won = true → IsQuorum cfg (granted (recordVote s.votes m.From' (!m.Reject'))) ∧
            peers ≡ₚ elements (cfg \ {[id]})) →
          (lost = true →
            ¬ IsQuorum cfg (cfg \ rejected (recordVote s.votes m.From' (!m.Reject')))) →
          s' = { prevoteRespResult id s m.From' m.Reject' won lost peers with prvals := pvs } →
          CandidateStepResult cfg id s m ents sv false s' := by
        intro s' won lost peers pvs Hw Hl Hs'
        simp only [CandidateStepResult, Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat,
          MsgBeat, MsgAppResp, MsgHeartbeatResp, MsgSnap, MsgPreVoteResp, Hrole]
        simp
        exact ⟨won, lost, peers, pvs, Hw, Hl, Hs'⟩
      rcases Hres with rfl | rfl | rfl
      · -- `quorum.VoteWon`: the real election, `campaign(campaignElection)`
        simp only [VoteWon]
        wp_pures; wp_load; wp_pures
        wp_apply raft.wp_load_state $$ Hphys as Hphys
        wp_pures
        rw [decide_eq_true (by simp only [Hrole]; decide)]
        wp_pures; wp_load; wp_pures; iclear r
        have Hnl1 : s.role ≠ .leader := by rw [Hrole]; decide
        have Hnw1 := Hpvnw Hrole Hty
        rw [show go_etcd_io.raft.v3.campaignElection = #campaignElection from rfl]
        wp_apply wp_raft_campaign _ _ _ { s with votes := recordVote s.votes m.From' (!m.Reject') }
            _ Hnl1 Hcfg Hnw1 $$ [$Hphys]
          as %peers %pvs ⟨%Hpeers, Hphys⟩
        wp_pures
        iapply HΦ $$ %GoInterface.nil %_ %false
        iframe Hphys
        simp only [Bool.false_eq_true, ↓reduceIte]
        ipureintro
        refine ⟨?_, trivial⟩
        refine Hres_pv _ true false peers pvs (fun _ => ⟨Hwon rfl, Hpeers⟩)
          (fun h => absurd h (by decide)) ?_
        rfl
      · -- `quorum.VoteLost`: step down at the unchanged term
        simp only [VoteLost]
        wp_pures; wp_load; wp_pures
        wp_apply raft.wp_load_Term $$ Hphys as Hphys
        wp_pures; wp_load; wp_pures; iclear r
        wp_apply wp_raft_becomeFollower $$ [$Hphys] as %pvs Hphys
        wp_pures
        iapply HΦ $$ %GoInterface.nil %_ %false
        iframe Hphys
        simp only [Bool.false_eq_true, ↓reduceIte]
        ipureintro
        refine ⟨?_, trivial⟩
        exact Hres_pv _ false true [] pvs (fun h => absurd h (by decide)) (fun _ => Hlost rfl) rfl
      · -- `quorum.VotePending`: keep waiting
        simp only [VotePending]
        wp_pures; iclear r
        iapply HΦ $$ %GoInterface.nil %_ %false
        iframe Hphys
        simp only [Bool.false_eq_true, ↓reduceIte]
        ipureintro
        refine ⟨?_, trivial⟩
        refine Hres_pv _ false false [] s.prvals (fun h => absurd h (by decide))
          (fun h => absurd h (by decide)) ?_
        cases s; rfl

end proof

end EtcdGrove
end Perennial
