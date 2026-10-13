/-
Port of election_proof/proof_stepCandidate.v.
-/
module

public import Spec.go_etcd_io.raft.v3.stepCandidate
public import Spec.go_etcd_io.raft.v3.raft__poll
public import Spec.go_etcd_io.raft.v3.raft__becomeLeader
public import Spec.go_etcd_io.raft.v3.raft__becomeFollower
public import Spec.go_etcd_io.raft.v3.raft__bcastAppend
public import Spec.go_etcd_io.raft.v3.raft__handleAppendEntries
public import Spec.go_etcd_io.raft.v3.raft__handleHeartbeat
public import Spec.go_etcd_io.raft.v3.raft__handleSnapshot
public import Spec.go_etcd_io.raft.v3.raft__campaign

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
/-- By type. `MsgProp`: `Infof`, then `return ErrProposalDropped` (the global's
points-to from `isInitialized_access`). `MsgApp`: `becomeFollower(m.Term, m.From)` with
`m.Term = s.term`, then `handleAppendEntries` at the follower state. `MsgHeartbeat`: the
same `becomeFollower`, then `handleHeartbeat`. `MsgBeat`, `MsgAppResp`,
`MsgHeartbeatResp`: no arm; nor `MsgReadIndex`, `MsgReadIndexResp` (2026-10-12).

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
  intro cfg r id s m ents sv voters cl Hty Hterm Hrole Happ Hhb Hpvnw
  wp_start as H
  iNamed H
  -- a candidate is a voter (`ownRaftPhys`'s `Hvoter`; until 2026-10-13 a premise)
  icases ownRaftPhys_voter cfg r id s $$ Hphys with ⟨%Hvoter, Hphys⟩
  have Hcfg : id ∈ cfg := Hvoter (by rcases Hrole with h | h <;> rw [h] <;> decide)
  ihave #Hinit := isInitialized_access $$ Hpkg
  unfold isInitialized
  icases Hinit with ⟨%e1, %e2, %e3, %e4, %errPropDropped, %gr, %_, %_, %_, %_, #Hinit⟩
  iNamed Hinit
  wp_auto
  -- `myVoteRespType`: `MsgPreVoteResp` for a pre-candidate, `MsgVoteResp` for a
  -- candidate; the two arms are joined
  wp_apply raft.wp_load_state $$ Hphys as Hphys
  have Hpre_iff : stateW64 s.role = W64 3 ↔ s.role = .preCandidate := by
    cases s.role <;> decide
  wp_join iprop(myVoteRespType_ptr ↦
      (if s.role = .preCandidate then W32 18 else W32 6))
    with [myVoteRespType] as myVoteRespType
  · rw [show raftpb.MsgPreVoteResp = #(W32 18) from rfl]
    wp_auto
    rw [if_pos (Hpre_iff.1 Hif)]
    iframe myVoteRespType
    ipureintro; exact rfl
  · rw [show raftpb.MsgVoteResp = #(W32 6) from rfl]
    wp_auto
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
  rcases Hty with Hty | Hty | Hty | Hty | Hty | Hty | Hty | Hty
  · -- `MsgVoteResp`: none of `MsgProp`, `MsgApp`, `MsgHeartbeat`, `MsgSnap`, so it falls
    -- through to `myVoteRespType`
    obtain ⟨Hterm', Hmnz⟩ := Hterm (Or.inl Hty)
    rw [Hty]
    simp only [MsgVoteResp]
    wp_auto
    rcases Hrole with Hrole | Hrole
    rotate_left
    · -- a pre-candidate: `myVoteRespType` is `MsgPreVoteResp`; a vote response is
      -- ignored
      rw [Hmp Hrole]
      wp_auto
      iapply HΦ $$ %GoInterface.nil %s %false
      iframe Hphys
      simp only [Bool.false_eq_true, ↓reduceIte]
      ipureintro
      refine ⟨?_, trivial⟩
      simp [CandidateStepResult, Hty, Hrole, MsgVoteResp]
    rw [Hmc (by rw [Hrole]; decide)]
    wp_auto
    have Hcfg_ne : cfg ≠ ∅ := fun h => GMap.not_elem_of_empty id (h ▸ Hcfg)
    wp_apply wp_raft_poll _ _ _ _ _ _ _ Hcfg_ne $$ [$Hphys]
      as %g %rj0 %res ⟨Hphys, %Hres, %Hwon, %Hlost⟩
    -- the `Infof` that follows reads `r.id`, `r.Term` and `r.logger`
    wp_apply raft.wp_load_id $$ Hphys as Hphys
    wp_raft_log
    rcases Hres with rfl | rfl | rfl
    · -- `quorum.VoteWon`: become leader and broadcast. `poll` does not touch the role,
      -- so we are still a candidate: not a pre-candidate, so this is `becomeLeader` and
      -- not `campaign`.
      simp only [VoteWon]
      wp_auto
      wp_apply raft.wp_load_state $$ Hphys as Hphys
      rw [decide_eq_false (by simp only [Hrole]; decide)]
      wp_auto
      wp_apply wp_raft_becomeLeader _ _ _ _ (by simp only [Hrole]; decide) Hcfg
          (by exact Hterm' ▸ Hmnz) $$ [$Hphys]
        as %pvs1 ⟨Hphys, %Hmb⟩
      -- `bcastAppend` adds *some* list of `App`s from `id` at the current term -- not one
      -- per peer; see `Spec/raft__bcastAppend.lean`.
      wp_apply wp_raft_bcastAppend $$ [$Hphys] as %ms %pvs ⟨Hphys, %Hms, %Hmm⟩
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
      wp_auto
      -- the `r.Term` the code passes is `s1`'s term
      wp_apply raft.wp_load_Term $$ Hphys as Hphys
      wp_apply wp_raft_becomeFollower _ _ _ _ _ _ (by exact Int.le_refl _) $$ [$Hphys] as %pvs Hphys
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
      wp_auto
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
    wp_auto
    wp_apply raft.wp_load_id $$ Hphys as Hphys
    wp_apply raft.wp_load_Term $$ Hphys as Hphys
    wp_raft_log
    iapply HΦ $$ %errPropDropped %s %true
    iframe Hphys
    simp only [↓reduceIte]
    isplitr
    · ipureintro
      simp [CandidateStepResult, Hty, MsgVoteResp, MsgProp]
    iexact ErrPropDropped
  · -- `MsgApp`: `becomeFollower(m.Term, m.From)`, then `handleAppendEntries`
    obtain ⟨Hwf, Hnw, Hconf, Hfid⟩ := Happ Hty
    have Hterm' := (Hterm (Or.inr (Or.inl Hty))).1
    rw [Hty]
    simp only [MsgApp]
    wp_auto
    wp_apply wp_raft_becomeFollower _ _ _ _ _ _
      (by exact Int.le_of_eq (congrArg (fun x : w64 => uint.Z x) Hterm'.symm)) $$ [$Hphys]
      as %pvs Hphys
    ihave Hes := Hents $$ %trivial
    icases Hes with ⟨#Hes, Hcap⟩
    wp_apply (raft.handleAppendEntries.spec_simple wp_raft_handleAppendEntries) _ _ _ { becomeFollower s m.Term' m.From' with prvals := pvs } _ _ Hwf Hnw Hconf
      Hfid $$ [$Hphys $Hes $Hcap]
      as %s' ⟨Hphys, %Hres⟩
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
    have Hterm' := (Hterm (Or.inr (Or.inr (Or.inl Hty)))).1
    rw [Hty]
    simp only [MsgHeartbeat]
    wp_auto
    wp_apply wp_raft_becomeFollower _ _ _ _ _ _
      (by exact Int.le_of_eq (congrArg (fun x : w64 => uint.Z x) Hterm'.symm)) $$ [$Hphys]
      as %pvs Hphys
    ihave #Hcl := Hctx $$ %(by simp [Hty, MsgHeartbeat, MsgProp])
    wp_apply (raft.handleHeartbeat.spec_simple wp_raft_handleHeartbeat) _ _ _ { becomeFollower s m.Term' m.From' with prvals := pvs } _
      cl Hcommit Hfrom $$ [$Hphys $Hcl] as Hphys
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
      simp only [MsgBeat, MsgAppResp, MsgHeartbeatResp] <;> wp_auto
    all_goals
      by_cases Hp : s.role = .preCandidate
      · rw [Hmp Hp]
        wp_auto
        iapply HΦ $$ %GoInterface.nil %s %false
        iframe Hphys
        simp only [Bool.false_eq_true, ↓reduceIte]
        ipureintro
        refine ⟨?_, trivial⟩
        simp [CandidateStepResult, Hty', MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
          MsgAppResp, MsgHeartbeatResp]
      · rw [Hmc Hp]
        wp_auto
        iapply HΦ $$ %GoInterface.nil %s %false
        iframe Hphys
        simp only [Bool.false_eq_true, ↓reduceIte]
        ipureintro
        refine ⟨?_, trivial⟩
        simp [CandidateStepResult, Hty', MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
          MsgAppResp, MsgHeartbeatResp]
  · -- `MsgSnap`: `becomeFollower(m.Term, m.From)`, then `handleSnapshot`
    have Hterm' := (Hterm (Or.inr (Or.inr (Or.inr Hty)))).1
    rw [Hty]
    ihave Hs := Hsnap $$ %rfl
    icases Hs with ⟨%learners, %Hsc, #Hsv, #Hvs, #Hls⟩
    obtain ⟨Hscope, Hfid⟩ := Hsc
    simp only [MsgSnap]
    wp_auto
    wp_apply wp_raft_becomeFollower _ _ _ _ _ _
      (by exact Int.le_of_eq (congrArg (fun x : w64 => uint.Z x) Hterm'.symm)) $$ [$Hphys]
      as %pvs Hphys
    wp_apply wp_raft_handleSnapshot _ _ _ { becomeFollower s m.Term' m.From' with prvals := pvs }
        _ sv voters learners rfl rfl Hcfg Hscope Hfid $$ [$Hphys $Hsv $Hvs $Hls]
      as %s' ⟨Hphys, %Hres⟩
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
    wp_auto
    rcases Hrole with Hrole | Hrole
    · -- a candidate: `myVoteRespType` is `MsgVoteResp`; a stale pre-vote response,
      -- ignored
      rw [Hmc (by rw [Hrole]; decide)]
      wp_auto
      iapply HΦ $$ %GoInterface.nil %s %false
      iframe Hphys
      simp only [Bool.false_eq_true, ↓reduceIte]
      ipureintro
      refine ⟨?_, trivial⟩
      simp [CandidateStepResult, Hty, Hrole, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat,
        MsgBeat, MsgAppResp, MsgHeartbeatResp, MsgSnap, MsgPreVoteResp]
    · -- a pre-candidate: `poll`, then win, lose or wait
      rw [Hmp Hrole]
      wp_auto
      have Hcfg_ne : cfg ≠ ∅ := fun h => GMap.not_elem_of_empty id (h ▸ Hcfg)
      wp_apply wp_raft_poll _ _ _ _ _ _ _ Hcfg_ne $$ [$Hphys]
        as %g %rj0 %res ⟨Hphys, %Hres, %Hwon, %Hlost⟩
      wp_apply raft.wp_load_id $$ Hphys as Hphys
      wp_raft_log
      have Hres_pv : ∀ (s' : NState) (won lost : Bool) (peers : List w64)
          (pvs : GMap w64 Progress),
          (won = true → IsQuorum cfg (granted (recordVote s.votes m.From' (!m.Reject'))) ∧
            peers ≡ₚ elements (cfg \ {[id]})) →
          (lost = true →
            ¬ IsQuorum cfg (cfg \ rejected (recordVote s.votes m.From' (!m.Reject')))) →
          s' = { prevoteRespResult id s m.From' m.Reject' won lost peers with prvals := pvs } →
          CandidateStepResult cfg id s m ents sv false s' cl := by
        intro s' won lost peers pvs Hw Hl Hs'
        simp only [CandidateStepResult, Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat,
          MsgBeat, MsgAppResp, MsgHeartbeatResp, MsgSnap, MsgPreVoteResp, Hrole]
        simp
        exact ⟨won, lost, peers, pvs, Hw, Hl, Hs'⟩
      rcases Hres with rfl | rfl | rfl
      · -- `quorum.VoteWon`: the real election, `campaign(campaignElection)`
        simp only [VoteWon]
        wp_auto
        wp_apply raft.wp_load_state $$ Hphys as Hphys
        rw [decide_eq_true (by simp only [Hrole]; decide)]
        wp_auto
        have Hnl1 : s.role ≠ .leader := by rw [Hrole]; decide
        have Hnw1 := Hpvnw Hrole Hty
        rw [show go_etcd_io.raft.v3.campaignElection = #campaignElection from rfl]
        wp_apply wp_raft_campaign _ _ _ { s with votes := recordVote s.votes m.From' (!m.Reject') }
            _ Hnl1 Hcfg Hnw1
            (fun h => by
              have := congrArg List.length h
              simp [campaignElection, campaignPreElection] at this)
            $$ [$Hphys]
          as %peers %pvs ⟨%Hpeers, Hphys⟩
        iapply HΦ $$ %GoInterface.nil %_ %false
        iframe Hphys
        simp only [Bool.false_eq_true, ↓reduceIte]
        ipureintro
        refine ⟨?_, trivial⟩
        refine Hres_pv _ true false peers pvs (fun _ => ⟨Hwon rfl, Hpeers⟩)
          (fun h => absurd h (by decide)) ?_
        have Htc : transferCtx campaignElection = [] := by
          simp (config := {decide := true}) [transferCtx, campaignElection, campaignTransfer]
        rw [Htc]
        rfl
      · -- `quorum.VoteLost`: step down at the unchanged term
        simp only [VoteLost]
        wp_auto
        wp_apply raft.wp_load_Term $$ Hphys as Hphys
        wp_apply wp_raft_becomeFollower _ _ _ _ _ _ (by exact Int.le_refl _) $$ [$Hphys]
          as %pvs Hphys
        iapply HΦ $$ %GoInterface.nil %_ %false
        iframe Hphys
        simp only [Bool.false_eq_true, ↓reduceIte]
        ipureintro
        refine ⟨?_, trivial⟩
        exact Hres_pv _ false true [] pvs (fun h => absurd h (by decide)) (fun _ => Hlost rfl) rfl
      · -- `quorum.VotePending`: keep waiting
        simp only [VotePending]
        wp_auto
        iapply HΦ $$ %GoInterface.nil %_ %false
        iframe Hphys
        simp only [Bool.false_eq_true, ↓reduceIte]
        ipureintro
        refine ⟨?_, trivial⟩
        refine Hres_pv _ false false [] s.prvals (fun h => absurd h (by decide))
          (fun h => absurd h (by decide)) ?_
        cases s; rfl

  · -- `MsgReadIndex`, `MsgReadIndexResp` (2026-10-12), and (2026-10-13) `MsgForgetLeader`,
    -- `MsgTransferLeader` and the local reports: no arm; `MsgTimeoutNow`: logged. In each case
    -- `myVoteRespType` is one of the two vote response types, neither of these
    rcases Hty with Hty' | Hty' | Hty' | Hty' | Hty' | Hty' | Hty' <;> rw [Hty'] <;>
      simp only [MsgReadIndex, MsgReadIndexResp, MsgForgetLeader, MsgTransferLeader,
        MsgTimeoutNow, MsgUnreachable, MsgSnapStatus] <;> wp_auto
    all_goals
      by_cases Hp : s.role = .preCandidate
      · rw [Hmp Hp]
        wp_auto
        try (
          wp_apply raft.wp_load_id $$ Hphys as Hphys
          wp_apply raft.wp_load_Term $$ Hphys as Hphys
          wp_apply raft.wp_load_state $$ Hphys as Hphys
          wp_raft_log)
        iapply HΦ $$ %GoInterface.nil %s %false
        iframe Hphys
        simp only [Bool.false_eq_true, ↓reduceIte]
        ipureintro
        refine ⟨?_, trivial⟩
        simp [CandidateStepResult, Hty', MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
          MsgAppResp, MsgHeartbeatResp, MsgSnap, MsgPreVoteResp, MsgReadIndex, MsgReadIndexResp,
          MsgForgetLeader, MsgTransferLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow]
      · rw [Hmc Hp]
        wp_auto
        try (
          wp_apply raft.wp_load_id $$ Hphys as Hphys
          wp_apply raft.wp_load_Term $$ Hphys as Hphys
          wp_apply raft.wp_load_state $$ Hphys as Hphys
          wp_raft_log)
        iapply HΦ $$ %GoInterface.nil %s %false
        iframe Hphys
        simp only [Bool.false_eq_true, ↓reduceIte]
        ipureintro
        refine ⟨?_, trivial⟩
        simp [CandidateStepResult, Hty', MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
          MsgAppResp, MsgHeartbeatResp, MsgSnap, MsgPreVoteResp, MsgReadIndex, MsgReadIndexResp,
          MsgForgetLeader, MsgTransferLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow]
end proof

end EtcdGrove
end Perennial
