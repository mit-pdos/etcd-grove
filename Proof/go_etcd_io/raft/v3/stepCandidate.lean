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
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetFrom
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTerm
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetReject
public import Proof.go_etcd_io.raft.v3.TracedUntraced
public import Proof.go_etcd_io.raft.v3.TracedUntracedStep
public import Proof.go_etcd_io.raft.v3.TracedUntracedSend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
`VotePending` leaves the state at `s1` and sends nothing.

raft v3.7 (2026-10-15, stage R4): the message's fields are read by its getters (`GetType`,
`GetFrom`, `GetTerm`, `GetReject`, callees), and `MsgApp`/`MsgHeartbeat`/`MsgSnap` hand the
received message (`msgIn`, entries read-only) to their handlers. -/
theorem stepCandidate.wp_proof
    (wp_raft_poll : raft.poll.spec (GF := GF) (hG := hG))
    (wp_raft_becomeLeader : raft.becomeLeader.spec (GF := GF) (hG := hG))
    (wp_raft_becomeFollower : raft.becomeFollower.spec (GF := GF) (hG := hG))
    (wp_raft_bcastAppend : raft.bcastAppend.spec (GF := GF) (hG := hG))
    (wp_raft_handleAppendEntries : raft.handleAppendEntries.spec (GF := GF) (hG := hG))
    (wp_raft_handleHeartbeat : raft.handleHeartbeat.spec (GF := GF) (hG := hG))
    (wp_raft_handleSnapshot : raft.handleSnapshot.spec (GF := GF) (hG := hG))
    (wp_raft_campaign : raft.campaign.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (wp_GetFrom : raftpb.Message.GetFrom.spec (GF := GF) (hG := hG))
    (wp_GetTerm : raftpb.Message.GetTerm.spec (GF := GF) (hG := hG))
    (wp_GetReject : raftpb.Message.GetReject.spec (GF := GF) (hG := hG)) :
    stepCandidate.spec (GF := GF) (hG := hG) := by
  -- (Q8 stage 1, slice 8) the gated specs, each arm consuming its gates; a `MsgSnap` untraced
  have wp_raft_becomeFollowerU := raft.becomeFollower.untraced wp_raft_becomeFollower
  intro c scfg r id s ml m ents sn rs sv cl G G' Gf G1 G2 Hty Hterm Hrole Happ Hhb Hpvnw Hsnap
    Hpinv Hidx' Hidx
  wp_start as H
  iNamed H
  -- the tag of the outcome, kept whole through the arms' rewriting of `m.Type'`
  generalize HHk : (m.Type' = MsgApp ∨ m.Type' = MsgHeartbeat ∨
    ((m.Type' = MsgVoteResp ∧ s.role = .candidate ∨
      m.Type' = MsgPreVoteResp ∧ s.role = .preCandidate) ∧
     (JQuorum c (granted (recordVote s.votes m.From' (!m.Reject'))) ∨
      JLost c (recordVote s.votes m.From' (!m.Reject'))))) = Hk
  -- the outcome is no gate's: `G` back, with the tag
  have Hnot : ∀ (P : Prop), m.Type' ≠ MsgApp → m.Type' ≠ MsgHeartbeat → ¬ P →
      ¬ (m.Type' = MsgApp ∨ m.Type' = MsgHeartbeat ∨ P) := by
    intro P h1 h2 h3 h
    rcases h with h | h | h
    · exact h1 h
    · exact h2 h
    · exact h3 h
  -- a candidate is a voter (`ownRaftPhys`'s `Hvoter`; until 2026-10-13 a premise)
  icases ownRaftPhysC_voter c r id s $$ Hphys with ⟨%Hvoter, Hphys⟩
  have Hcfg : id ∈ c.voters :=
    Hvoter (by rcases Hrole with h | h <;> rw [h] <;> decide) (by rcases Hrole with h | h <;> rw [h] <;> decide)
  ihave #Hinit := isInitialized_access $$ Hpkg
  unfold isInitialized
  icases Hinit with ⟨%e1, %e2, %e3, %e4, %errPropDropped, %gr, %_, %_, %_, %_, #Hinit⟩
  iNamed Hinit
  wp_auto
  -- `myVoteRespType`: `MsgPreVoteResp` for a pre-candidate, `MsgVoteResp` for a
  -- candidate; the two arms are joined
  wp_apply raft.wp_load_stateC $$ Hphys as Hphys
  have Hpre_iff : stateW64 s.role = W64 3 ↔ s.role = .preCandidate := by
    cases s.role <;> decide
  wp_join iprop(myVoteRespType_ptr ↦
      (if s.role = .preCandidate then W32 18 else W32 6))
    with [myVoteRespType] as myVoteRespType
  · try rw [show raftpb.MsgPreVoteResp = #(W32 18) from rfl]
    try wp_auto
    rw [ite_eq_left (Hpre_iff.1 Hif)]
    iframe myVoteRespType
    try (ipureintro; exact rfl)
  · try rw [show raftpb.MsgVoteResp = #(W32 6) from rfl]
    try wp_auto
    rw [ite_eq_right (fun h => Hif (Hpre_iff.2 h))]
    iframe myVoteRespType
    try (ipureintro; exact rfl)
  -- kept opaque below, so that the arms' `decide` rewrites find the program's
  -- comparisons and not this one
  generalize Hmvr : (if s.role = .preCandidate then W32 18 else W32 6) = mvr
  have Hmp : s.role = .preCandidate → mvr = W32 18 := by
    intro Hp; rw [← Hmvr, ite_eq_left Hp]
  have Hmc : s.role ≠ .preCandidate → mvr = W32 6 := by
    intro Hp; rw [← Hmvr, ite_eq_right Hp]
  clear Hmvr
  wp_apply wp_GetType.1 ml _ _ _ _ $$ [$Hm] as Hm
  rcases Hty with Hty | Hty | Hty | Hty | Hty | Hty | Hty | Hty
  · -- `MsgVoteResp`: none of `MsgProp`, `MsgApp`, `MsgHeartbeat`, `MsgSnap`, so it falls
    -- through to `myVoteRespType`
    obtain ⟨Hterm', Hmnz⟩ := Hterm (Or.inl Hty)
    have Hna : m.Type' ≠ MsgApp := by rw [Hty]; simp [MsgVoteResp, MsgApp]
    have Hnh : m.Type' ≠ MsgHeartbeat := by rw [Hty]; simp [MsgVoteResp, MsgHeartbeat]
    have Hnpv : m.Type' ≠ MsgPreVoteResp := by rw [Hty]; simp [MsgVoteResp, MsgPreVoteResp]
    simp only [Hty, MsgVoteResp]
    wp_auto
    rcases Hrole with Hrole | Hrole
    rotate_left
    · -- a pre-candidate: `myVoteRespType` is `MsgPreVoteResp`; a vote response is
      -- ignored
      rw [Hmp Hrole]
      wp_auto
      iapply HΦ $$ %GoInterface.nil %s %false %c
      iframe Hphys
      simp only [Bool.false_eq_true, ↓reduceIte]
      isplitr [HG]
      · ipureintro
        unfold CandidateStepResultC
        refine ⟨by simp [Hty, MsgVoteResp, MsgSnap], ?_⟩
        simp [Hty, Hrole, MsgVoteResp]
      isplitr [HG]
      · ipureintro; first | rfl | trivial
      iright
      isplitr
      · ipureintro
        rw [← HHk]
        refine Hnot _ Hna Hnh ?_
        rintro ⟨⟨_, h⟩ | ⟨h, _⟩, _⟩
        · rw [Hrole] at h; exact absurd h (by decide)
        · exact Hnpv h
      iidx HG
    rw [Hmc (by rw [Hrole]; decide)]
    wp_auto
    wp_apply wp_GetFrom.1 ml _ _ _ _ $$ [$Hm] as Hm
    wp_apply wp_GetType.1 ml _ _ _ _ $$ [$Hm] as Hm
    wp_apply wp_GetReject.1 ml _ _ _ _ $$ [$Hm] as Hm
    wp_apply wp_raft_poll _ _ _ _ _ _ _ $$ [$Hphys]
      as %g %rj0 %res ⟨Hphys, %Hres, %Hwon, %Hlost⟩
    -- the `Infof` that follows reads `r.id`, `r.Term` and `r.logger`
    wp_apply raft.wp_load_idC $$ Hphys as Hphys
    wp_apply wp_GetType.1 ml _ _ _ _ $$ [$Hm] as Hm
    wp_raft_logC
    rcases Hres with rfl | rfl | rfl
    · -- `quorum.VoteWon`: become leader and broadcast. `poll` does not touch the role,
      -- so we are still a candidate: not a pre-candidate, so this is `becomeLeader` and
      -- not `campaign`.
      have Hwin : m.Type' = MsgVoteResp ∧ s.role = .candidate ∧
          JQuorum c (granted (recordVote s.votes m.From' (!m.Reject'))) := ⟨Hty, Hrole, Hwon.1 rfl⟩
      simp only [VoteWon]
      wp_auto
      wp_apply raft.wp_load_stateC $$ Hphys as Hphys
      rw [decide_eq_false (by simp only [Hrole]; decide)]
      wp_auto
      ispecialize Hgbl $$ %(⟨trivial, Hwin.2⟩)
      wp_apply wp_raft_becomeLeader c r id _ (G s.outbox) G1 G2
          (G' (s.outbox ++ [selfAck id (becomeLeaderLog id { s with votes := recordVote s.votes m.From' (!m.Reject') })])) (by simp only [Hrole]; decide)
          (by simp only [Hrole]; decide) (by exact Hterm' ▸ Hmnz) $$ [$Hphys $HG $Hgbl $Hgrep $Hgack]
        as %pvs1 ⟨Hphys, %Hmb, HG⟩
      -- `bcastAppend` adds *some* list of `App`s from `id` at the current term -- not one
      -- per peer; see `Spec/raft__bcastAppend.lean`.
      ihave #Hgc := Hgcast $$ %(⟨trivial, Hwin.2⟩)
      ihave HG : G' ({ becomeLeader id { s with votes := recordVote s.votes m.From' (!m.Reject') }
          with prvals := pvs1 } : NState).outbox $$ [HG]
      · iidx HG
      ihave #Hgate : □ (∀ (to : w64) (mm : Msg) (o : List Msg),
          ⌜to ≠ id ∧ to ∈ domSet ({ becomeLeader id { s with votes := recordVote s.votes m.From' (!m.Reject') }
            with prvals := pvs1 } : NState).progress⌝ -∗
          ⌜AppOk id (toPState { becomeLeader id { s with votes := recordVote s.votes m.From' (!m.Reject') }
              with prvals := pvs1 }) mm ∧
            mm.commit = (toPState { becomeLeader id { s with votes := recordVote s.votes m.From' (!m.Reject') }
              with prvals := pvs1 }).commit ∧ mm.dst = to ∧
            uint.Z ((prvalsMatch pvs1 !! to).getD (W64 0)) ≤ uint.Z mm.index ∧ mm.rejecthint = W64 0⌝ -∗ G' o -∗
          HookGateOpt ({ becomeLeader id { s with votes := recordVote s.votes m.From' (!m.Reject') }
              with prvals := pvs1 } : NState).gh.tr r
            (sendOutGate id { becomeLeader id { s with votes := recordVote s.votes m.From' (!m.Reject') }
              with prvals := pvs1 } c MsgApp [mm]) (G' (o ++ [mm]))) $$ []
      · rw [show ({ becomeLeader id { s with votes := recordVote s.votes m.From' (!m.Reject') } with prvals := pvs1 } : NState).gh = s.gh from rfl]
        imodintro
        iintro %to %mm %o %Hto %Hmm HG
        ispecialize Hgc $$ %pvs1 %to %mm %o %Hto %Hmm HG
        iapply hookGateOpt_congr _ _ r _ _ _ (by rfl) (by rfl) $$ Hgc
      ihave #Hnosnap2 : TrNoSnap (GF := GF)
          ({ becomeLeader id { s with votes := recordVote s.votes m.From' (!m.Reject') }
            with prvals := pvs1 } : NState).gh.tr
          ({ becomeLeader id { s with votes := recordVote s.votes m.From' (!m.Reject') }
            with prvals := pvs1 } : NState).logst $$ []
      · rw [show ({ becomeLeader id { s with votes := recordVote s.votes m.From' (!m.Reject') } with prvals := pvs1 } : NState).gh = s.gh from rfl,
          show TrNoSnap (GF := GF) s.gh.tr ({ becomeLeader id { s with votes := recordVote s.votes m.From' (!m.Reject') } with prvals := pvs1 } : NState).logst = TrNoSnap s.gh.tr s.logst from rfl]
        iexact Hnosnap
      wp_apply wp_raft_bcastAppend c r id
        { becomeLeader id { s with votes := recordVote s.votes m.From' (!m.Reject') } with prvals := pvs1 }
        G' (by rfl)
        (by first | exact Hterm' ▸ Hmnz | (simp only [becomeLeader, resetTo, resetTo0]; exact Hterm' ▸ Hmnz) | simp_all)
        Hidx'
        $$ [$Hphys $HG $Hgate $Hnosnap2] as %ms %pvs ⟨Hphys, %Hms, %Hmm, HG⟩
      iapply HΦ $$ %GoInterface.nil %_ %false %c
      iframe Hphys
      simp only [Bool.false_eq_true, ↓reduceIte]
      isplitr [HG]
      · ipureintro
        unfold CandidateStepResultC
        refine ⟨by simp [Hty, MsgVoteResp, MsgSnap], ?_⟩
        simp only [Hty, Hrole, ↓reduceIte]
        refine ⟨trivial, ?_⟩
        have Hnp : ¬ (PRole.candidate = PRole.preCandidate) := by decide
        simp only [Hnp, ↓reduceIte]
        refine ⟨true, false, ms, pvs, fun _ => ⟨Hwon.1 rfl, ?_, ?_⟩, fun h => absurd h (by decide),
          fun h => absurd h (by decide), ?_⟩
        · exact (replSends_prvals _ _ pvs1 ms).1 Hms
        · rw [Hmm]; exact Hmb
        · cases s; rfl
      isplitr [HG]
      · ipureintro; first | rfl | trivial
      ileft
      isplitr
      · ipureintro
        rw [← HHk]
        exact Or.inr (Or.inr ⟨Or.inl ⟨Hty, Hrole⟩, Or.inl (Hwon.1 rfl)⟩)
      iidx HG
    · -- `quorum.VoteLost`: step down at the unchanged term
      simp only [VoteLost]
      wp_auto
      -- the `r.Term` the code passes is `s1`'s term
      wp_apply raft.wp_load_TermC $$ Hphys as Hphys
      have Hlo : (m.Type' = MsgVoteResp ∧ s.role = .candidate ∨
          m.Type' = MsgPreVoteResp ∧ s.role = .preCandidate) ∧
          JLost c (recordVote s.votes m.From' (!m.Reject')) := ⟨Or.inl ⟨Hty, Hrole⟩, Hlost.1 rfl⟩
      ispecialize Hglost $$ %(by first | exact ⟨Or.inl ⟨trivial, Hrole⟩, Hlost.1 rfl⟩ | exact ⟨Or.inr ⟨trivial, Hrole⟩, Hlost.1 rfl⟩) HG
      wp_apply wp_raft_becomeFollower c r id _ _ _ (G' s.outbox) (by exact Int.le_refl _) (fun _ => rfl)
        $$ [$Hphys $Hglost] as %pvs ⟨Hphys, HG⟩
      iapply HΦ $$ %GoInterface.nil %_ %false %c
      iframe Hphys
      simp only [Bool.false_eq_true, ↓reduceIte]
      isplitr [HG]
      · ipureintro
        unfold CandidateStepResultC
        refine ⟨by simp [Hty, MsgVoteResp, MsgSnap], ?_⟩
        simp only [Hty, Hrole, ↓reduceIte]
        refine ⟨trivial, ?_⟩
        have Hnp : ¬ (PRole.candidate = PRole.preCandidate) := by decide
        simp only [Hnp, ↓reduceIte]
        refine ⟨false, true, [], pvs, fun h => absurd h (by decide), fun _ => Hlost.1 rfl, fun _ _ => rfl, ?_⟩
        cases s; rfl
      isplitr [HG]
      · ipureintro; first | rfl | trivial
      ileft
      isplitr
      · ipureintro
        rw [← HHk]
        exact Or.inr (Or.inr ⟨Or.inl ⟨Hty, Hrole⟩, Or.inr (Hlost.1 rfl)⟩)
      iidx HG
    · -- `quorum.VotePending`: neither switch arm fires; keep waiting
      simp only [VotePending]
      wp_auto
      iapply HΦ $$ %GoInterface.nil %_ %false %c
      iframe Hphys
      simp only [Bool.false_eq_true, ↓reduceIte]
      isplitr [HG]
      · ipureintro
        unfold CandidateStepResultC
        refine ⟨by simp [Hty, MsgVoteResp, MsgSnap], ?_⟩
        simp only [Hty, Hrole, ↓reduceIte]
        refine ⟨trivial, ?_⟩
        have Hnp : ¬ (PRole.candidate = PRole.preCandidate) := by decide
        simp only [Hnp, ↓reduceIte]
        -- nothing wrote a `Progress`: the values are `s1`'s own
        refine ⟨false, false, [], s.prvals, fun h => absurd h (by decide),
          fun h => absurd h (by decide), fun _ h => absurd (Hlost.2 h) (by decide), ?_⟩
        cases s; simp only at Hrole; subst Hrole; rfl
      isplitr [HG]
      · ipureintro; first | rfl | trivial
      iright
      isplitr
      · ipureintro
        rw [← HHk]
        refine Hnot _ Hna Hnh ?_
        rintro ⟨_, h | h⟩
        · exact absurd (Hwon.2 h) (by decide)
        · exact absurd (Hlost.2 h) (by decide)
      iidx HG
  · -- `MsgProp`: no leader to forward to; dropped
    have Hna : m.Type' ≠ MsgApp := by rw [Hty]; simp [MsgProp, MsgApp]
    have Hnh : m.Type' ≠ MsgHeartbeat := by rw [Hty]; simp [MsgProp, MsgHeartbeat]
    have Hnv : m.Type' ≠ MsgVoteResp := by rw [Hty]; simp [MsgProp, MsgVoteResp]
    have Hnpv : m.Type' ≠ MsgPreVoteResp := by rw [Hty]; simp [MsgProp, MsgPreVoteResp]
    simp only [Hty, MsgProp]
    wp_auto
    wp_apply raft.wp_load_idC $$ Hphys as Hphys
    wp_apply raft.wp_load_TermC $$ Hphys as Hphys
    wp_raft_logC
    iapply HΦ $$ %errPropDropped %s %true %c
    iframe Hphys
    simp only [↓reduceIte]
    isplitr [HG]
    · ipureintro
      unfold CandidateStepResultC
      refine ⟨by simp [Hty, MsgProp, MsgSnap], ?_⟩
      simp [Hty, MsgVoteResp, MsgProp]
    isplitr [HG]
    · iexact ErrPropDropped
    iright
    isplitr
    · ipureintro
      rw [← HHk]
      refine Hnot _ Hna Hnh ?_
      rintro ⟨⟨h, _⟩ | ⟨h, _⟩, _⟩
      · exact Hnv h
      · exact Hnpv h
    iidx HG
  · -- `MsgApp`: `becomeFollower(m.Term, m.From)`, then `handleAppendEntries`
    obtain ⟨Hwf, Hnw, Hconf, Hfid⟩ := Happ Hty
    have Hterm' := (Hterm (Or.inr (Or.inl Hty))).1
    rw [show (if m.Type' = MsgProp then DFrac.own 1 else DFrac.discard) = DFrac.discard by
      simp [Hty, MsgApp, MsgProp]]
    simp only [Hty, MsgApp]
    wp_auto
    wp_apply wp_GetTerm.1 ml _ _ _ _ $$ [$Hm] as Hm
    wp_apply wp_GetFrom.1 ml _ _ _ _ $$ [$Hm] as Hm
    ihave Hgbf2 : HookGate s.gh.tr r (NodeEvOf (W64 2) id (becomeFollower s m.Term' m.From') c) Gf
        $$ [Hgbf HG]
    · rw [Hterm']
      iapply Hgbf $$ %(by first | exact Or.inl trivial | exact Or.inr trivial) HG
    wp_apply wp_raft_becomeFollower c r id s m.Term' m.From' Gf
      (by exact Int.le_of_eq (congrArg (fun x : w64 => uint.Z x) Hterm'.symm)) (fun _ => rfl)
      $$ [$Hphys $Hgbf2] as %pvs ⟨Hphys, HGf⟩
    ihave Hga : ∀ (s1 : NState) (mm : Msg),
        ⌜HandleAppResult id ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState) m ents
          (sendMsgs s1 [mm])⌝ -∗
        Gf -∗ HookGateOpt ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState).gh.tr r
          (sendOutGate id s1 c MsgAppResp [mm]) (G' (sendMsgs s1 [mm]).outbox) $$ [Hgapp]
    · rw [Hterm']
      iintro %s1 %mm %Hr HGf
      ispecialize Hgapp $$ %trivial %pvs %s1 %mm %Hr HGf
      iapply hookGateOpt_congr _ _ r _ _ _ (by rfl) (by rfl) $$ Hgapp
    wp_apply wp_raft_handleAppendEntries _ _ _ { becomeFollower s m.Term' m.From' with prvals := pvs }
      ml m ents sn cl rs Gf G' Hwf Hnw Hconf Hfid Hty (fun h => by simp [becomeFollower] at h)
      (by simp only [becomeFollower, resetTo, resetTo0]; exact (Hterm (Or.inr (Or.inl Hty))).2)
      $$ [$Hphys $Hm $HGf $Hga]
      as %s' ⟨Hphys, %Hres, HG⟩
    iapply HΦ $$ %GoInterface.nil %s' %false %c
    iframe Hphys
    simp only [Bool.false_eq_true, ↓reduceIte]
    isplitr [HG]
    · ipureintro
      unfold CandidateStepResultC
      refine ⟨by simp [Hty, MsgApp, MsgSnap], ?_⟩
      simp only [Hty, MsgVoteResp, MsgProp, MsgApp]
      refine ⟨trivial, pvs, ?_⟩
      rw [← Hterm']
      exact Hres
    isplitr [HG]
    · ipureintro; first | rfl | trivial
    ileft
    isplitr
    · ipureintro
      rw [← HHk]
      exact Or.inl Hty
    iidx HG
  · -- `MsgHeartbeat`: `becomeFollower(m.Term, m.From)`, then `handleHeartbeat`
    obtain ⟨Hcommit, Hfrom⟩ := Hhb Hty
    have Hterm' := (Hterm (Or.inr (Or.inr (Or.inl Hty)))).1
    simp only [Hty, MsgHeartbeat]
    wp_auto
    wp_apply wp_GetTerm.1 ml _ _ _ _ $$ [$Hm] as Hm
    wp_apply wp_GetFrom.1 ml _ _ _ _ $$ [$Hm] as Hm
    ihave Hgbf2 : HookGate s.gh.tr r (NodeEvOf (W64 2) id (becomeFollower s m.Term' m.From') c) Gf
        $$ [Hgbf HG]
    · rw [Hterm']
      iapply Hgbf $$ %(by first | exact Or.inl trivial | exact Or.inr trivial) HG
    wp_apply wp_raft_becomeFollower c r id s m.Term' m.From' Gf
      (by exact Int.le_of_eq (congrArg (fun x : w64 => uint.Z x) Hterm'.symm)) (fun _ => rfl)
      $$ [$Hphys $Hgbf2] as %pvs ⟨Hphys, HGf⟩
    ihave Hgh : Gf -∗ HookGateOpt ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState).gh.tr r
        (sendOutGate id { ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState) with
            logst := { ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState).logst with
              committed := plogCommitTo
                ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState).logst.committed m.Commit' } }
          c MsgHeartbeatResp
          [{ Msg.plain .heartbeatResp id m.From'
              ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState).term false with ctx := cl }])
        (G' (s.outbox ++ [{ Msg.plain .heartbeatResp id m.From' s.term false with ctx := cl }])) $$ [Hghb]
    · rw [Hterm']
      iintro HGf
      ispecialize Hghb $$ %trivial %pvs HGf
      iapply hookGateOpt_congr _ _ r _ _ _ (by rfl) (by rfl) $$ Hghb
    wp_apply wp_raft_handleHeartbeat _ _ _ { becomeFollower s m.Term' m.From' with prvals := pvs }
      ml _ _ _ m ents sn cl rs Gf (G' (s.outbox ++ [{ Msg.plain .heartbeatResp id m.From' s.term false with ctx := cl }])) Hcommit Hfrom
      (by simp only [becomeFollower, resetTo, resetTo0]; exact (Hterm (Or.inr (Or.inr (Or.inl Hty)))).2)
      $$ [$Hphys $Hm $HGf $Hgh] as ⟨Hphys, -, HG⟩
    iapply HΦ $$ %GoInterface.nil %_ %false %c
    iframe Hphys
    simp only [Bool.false_eq_true, ↓reduceIte]
    isplitr [HG]
    · ipureintro
      unfold CandidateStepResultC
      refine ⟨by simp [Hty, MsgHeartbeat, MsgSnap], ?_⟩
      simp only [Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat]
      refine ⟨trivial, pvs, ?_⟩
      rw [← Hterm']
    isplitr [HG]
    · ipureintro; first | rfl | trivial
    ileft
    isplitr
    · ipureintro
      rw [← HHk]
      exact Or.inr (Or.inl Hty)
    iapply idx_eq _ ?_ $$ HG
    simp [heartbeatResult, sendMsgs, becomeFollower, resetTo, resetTo0, Hterm', Msg.plain]
  · -- `MsgBeat`, `MsgAppResp`, `MsgHeartbeatResp`: no arm; `myVoteRespType` is one of
    -- the two response types, neither of these
    have Hnh0 : ¬ (m.Type' = MsgApp ∨ m.Type' = MsgHeartbeat ∨
        ((m.Type' = MsgVoteResp ∧ s.role = .candidate ∨
          m.Type' = MsgPreVoteResp ∧ s.role = .preCandidate) ∧
         (JQuorum c (granted (recordVote s.votes m.From' (!m.Reject'))) ∨
          JLost c (recordVote s.votes m.From' (!m.Reject'))))) := by
      rcases Hty with Hty' | Hty' | Hty' | Hty' <;> rw [Hty'] <;>
        simp [MsgBeat, MsgAppResp, MsgHeartbeatResp, MsgCheckQuorum, MsgApp, MsgHeartbeat,
          MsgVoteResp, MsgPreVoteResp]
    rcases Hty with Hty' | Hty' | Hty' | Hty' <;> rw [Hty'] <;>
      simp only [MsgBeat, MsgAppResp, MsgHeartbeatResp, MsgCheckQuorum] <;> wp_auto
    all_goals
      by_cases Hp : s.role = .preCandidate
      · rw [Hmp Hp]
        wp_auto
        iapply HΦ $$ %GoInterface.nil %s %false %c
        iframe Hphys
        simp only [Bool.false_eq_true, ↓reduceIte]
        isplitr [HG]
        · ipureintro
          unfold CandidateStepResultC
          refine ⟨by simp [Hty', MsgBeat, MsgAppResp, MsgHeartbeatResp, MsgCheckQuorum, MsgSnap], ?_⟩
          simp [Hty', MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
            MsgAppResp, MsgHeartbeatResp, MsgCheckQuorum]
        isplitr [HG]
        · ipureintro; first | rfl | trivial
        iright
        isplitr
        · ipureintro
          rw [← HHk]
          exact Hnh0
        iidx HG
      · rw [Hmc Hp]
        wp_auto
        iapply HΦ $$ %GoInterface.nil %s %false %c
        iframe Hphys
        simp only [Bool.false_eq_true, ↓reduceIte]
        isplitr [HG]
        · ipureintro
          unfold CandidateStepResultC
          refine ⟨by simp [Hty', MsgBeat, MsgAppResp, MsgHeartbeatResp, MsgCheckQuorum, MsgSnap], ?_⟩
          simp [Hty', MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
            MsgAppResp, MsgHeartbeatResp, MsgCheckQuorum]
        isplitr [HG]
        · ipureintro; first | rfl | trivial
        iright
        isplitr
        · ipureintro
          rw [← HHk]
          exact Hnh0
        iidx HG
  · -- `MsgSnap`: `becomeFollower(m.Term, m.From)`, then `handleSnapshot` (untraced only)
    have Hterm' := (Hterm (Or.inr (Or.inr (Or.inr Hty)))).1
    obtain ⟨Hsn, Hscfg, Hscope, Hfid, Hns, Htr⟩ := Hsnap Hty
    have Hnh0 : ¬ (m.Type' = MsgApp ∨ m.Type' = MsgHeartbeat ∨
        ((m.Type' = MsgVoteResp ∧ s.role = .candidate ∨
          m.Type' = MsgPreVoteResp ∧ s.role = .preCandidate) ∧
         (JQuorum c (granted (recordVote s.votes m.From' (!m.Reject'))) ∨
          JLost c (recordVote s.votes m.From' (!m.Reject'))))) := by
      rw [Hty]; simp [MsgSnap, MsgApp, MsgHeartbeat, MsgVoteResp, MsgPreVoteResp]
    rw [show (if m.Type' = MsgProp then DFrac.own 1 else DFrac.discard) = DFrac.discard by
      simp [Hty, MsgSnap, MsgProp]]
    simp only [Hty, MsgSnap]
    wp_auto
    wp_apply wp_GetTerm.1 ml _ _ _ _ $$ [$Hm] as Hm
    wp_apply wp_GetFrom.1 ml _ _ _ _ $$ [$Hm] as Hm
    wp_apply wp_raft_becomeFollowerU _ _ _ _ _ _
      (by exact Int.le_of_eq (congrArg (fun x : w64 => uint.Z x) Hterm'.symm)) (by tr_none) $$ [$Hphys]
      as %pvs Hphys
    -- (2026-10-14) at any configuration: `handleSnapshot` on the struct at `c`
    ihave #Hcs : ksnCert (GF := GF) ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState).gh.sn
        (snapTrip sv sv.Metadata'.ConfState'.lists) $$ []
    · iunfold rcvSrc at Hcert
      icases Hcert with (%Hn | ⟨%sv', %Hsv', #Hc⟩)
      · exact (Hn rfl).elim
      · rw [Hsn] at Hsv'; obtain rfl := Option.some.inj Hsv'
        rw [show ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState).gh.sn =
          s.gh.sn by simp [becomeFollower, resetTo, resetTo0]]
        iexact Hc
    wp_apply wp_raft_handleSnapshot c _ _ { becomeFollower s m.Term' m.From' with prvals := pvs }
        ml m ents sn cl rs sv scfg rfl rfl Hsn Hscfg Hscope Hfid Hns
        (by simp only [becomeFollower, resetTo, resetTo0]; first | exact (Hterm (Or.inr (Or.inl Hty))).2 | exact (Hterm (Or.inr (Or.inr (Or.inl Hty)))).2 | exact (Hterm (Or.inr (Or.inr (Or.inr Hty)))).2) (by tr_none) $$ [$Hphys $Hm $Hcs]
      as %s' ⟨Hphys, %Hres⟩
    -- (2026-11-10, slice 14) untraced: the caller's resource ignores the outbox
    ihave HG : G s'.outbox $$ [HG]
    · rw [Hidx Htr s'.outbox s.outbox]; iexact HG
    iapply HΦ $$ %GoInterface.nil %s' %false %c
    iframe Hphys
    simp only [Bool.false_eq_true, ↓reduceIte]
    isplitr [HG]
    · ipureintro
      unfold CandidateStepResultC
      refine ⟨rfl, ?_⟩
      simp only [Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
        MsgAppResp, MsgHeartbeatResp, MsgCheckQuorum, MsgSnap]
      refine ⟨trivial, pvs, ?_⟩
      rw [← Hterm']
      exact Hres
    isplitr [HG]
    · ipureintro; first | rfl | trivial
    iright
    isplitr
    · ipureintro
      rw [← HHk]
      exact Hnh0
    iidx HG
  · -- `MsgPreVoteResp` (2026-10-04)
    have Hna : m.Type' ≠ MsgApp := by rw [Hty]; simp [MsgPreVoteResp, MsgApp]
    have Hnh : m.Type' ≠ MsgHeartbeat := by rw [Hty]; simp [MsgPreVoteResp, MsgHeartbeat]
    have Hnv : m.Type' ≠ MsgVoteResp := by rw [Hty]; simp [MsgPreVoteResp, MsgVoteResp]
    simp only [Hty, MsgPreVoteResp]
    wp_auto
    rcases Hrole with Hrole | Hrole
    · -- a candidate: `myVoteRespType` is `MsgVoteResp`; a stale pre-vote response,
      -- ignored
      rw [Hmc (by rw [Hrole]; decide)]
      wp_auto
      iapply HΦ $$ %GoInterface.nil %s %false %c
      iframe Hphys
      simp only [Bool.false_eq_true, ↓reduceIte]
      isplitr [HG]
      · ipureintro
        unfold CandidateStepResultC
        refine ⟨by simp [Hty, MsgSnap, MsgPreVoteResp], ?_⟩
        simp [Hty, Hrole, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat,
          MsgBeat, MsgAppResp, MsgHeartbeatResp, MsgCheckQuorum, MsgSnap, MsgPreVoteResp]
      isplitr [HG]
      · ipureintro; first | rfl | trivial
      iright
      isplitr
      · ipureintro
        rw [← HHk]
        refine Hnot _ Hna Hnh ?_
        rintro ⟨⟨h, _⟩ | ⟨_, h⟩, _⟩
        · exact Hnv h
        · rw [Hrole] at h; exact absurd h (by decide)
      iidx HG
    · -- a pre-candidate: `poll`, then win, lose or wait
      rw [Hmp Hrole]
      wp_auto
      wp_apply wp_GetFrom.1 ml _ _ _ _ $$ [$Hm] as Hm
      wp_apply wp_GetType.1 ml _ _ _ _ $$ [$Hm] as Hm
      wp_apply wp_GetReject.1 ml _ _ _ _ $$ [$Hm] as Hm
      wp_apply wp_raft_poll _ _ _ _ _ _ _ $$ [$Hphys]
        as %g %rj0 %res ⟨Hphys, %Hres, %Hwon, %Hlost⟩
      wp_apply raft.wp_load_idC $$ Hphys as Hphys
      wp_apply wp_GetType.1 ml _ _ _ _ $$ [$Hm] as Hm
      wp_raft_logC
      have Hres_pv : ∀ (s' : NState) (won lost : Bool) (peers : List w64)
          (pvs : GMap w64 Progress),
          (won = true → JQuorum c (granted (recordVote s.votes m.From' (!m.Reject'))) ∧
            peers ≡ₚ elements (c.voters \ {[id]})) →
          (lost = true →
            JLost c (recordVote s.votes m.From' (!m.Reject'))) →
          s' = { prevoteRespResult id s m.From' m.Reject' won lost peers with prvals := pvs } →
          CandidateStepResultC c scfg id s m ents sv false s' c cl := by
        intro s' won lost peers pvs Hw Hl Hs'
        unfold CandidateStepResultC
        refine ⟨by simp [Hty, MsgSnap, MsgPreVoteResp], ?_⟩
        simp only [Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat,
          MsgBeat, MsgAppResp, MsgHeartbeatResp, MsgCheckQuorum, MsgSnap, MsgPreVoteResp, Hrole]
        simp
        exact ⟨won, lost, peers, pvs, Hw, Hl, Hs'⟩
      rcases Hres with rfl | rfl | rfl
      · -- `quorum.VoteWon`: the real election, `campaign(campaignElection)`
        have Hwin : m.Type' = MsgPreVoteResp ∧ s.role = .preCandidate ∧
            JQuorum c (granted (recordVote s.votes m.From' (!m.Reject'))) := ⟨Hty, Hrole, Hwon.1 rfl⟩
        simp only [VoteWon]
        wp_auto
        wp_apply raft.wp_load_stateC $$ Hphys as Hphys
        rw [decide_eq_true (by simp only [Hrole]; decide)]
        wp_auto
        have Hnl1 : s.role ≠ .leader := by rw [Hrole]; decide
        have Hnw1 := Hpvnw Hrole Hty
        have Hde : decide (campaignElection = campaignPreElection) = false := by
          simp (config := {decide := true}) [campaignElection, campaignPreElection]
        have Htc : transferCtx campaignElection = [] := by
          simp (config := {decide := true}) [transferCtx, campaignElection, campaignTransfer]
        ihave Hgbc : G s.outbox -∗ (if campaignElection = campaignPreElection then iprop(|={⊤}=> G' ({ s with votes := recordVote s.votes m.From' (!m.Reject') } : NState).outbox)
            else HookGate ({ s with votes := recordVote s.votes m.From' (!m.Reject') } : NState).gh.tr r
              (NodeEvOf (W64 1) id (becomeCandidate id { s with votes := recordVote s.votes m.From' (!m.Reject') })
                c) (G' ({ s with votes := recordVote s.votes m.From' (!m.Reject') } : NState).outbox)) $$ [Hgcamp]
        · simp only [eq_false (show ¬ _ from by simpa using Hde), ite_false]
          iintro HG
          iapply hookGate_congrQ _ _ r _ _ (G' s.outbox) _ (by rfl) (by rfl) (by rfl)
          iapply Hgcamp $$ %(⟨trivial, Hwin.2⟩) HG
        ihave #Hgsend : □ (∀ (pvs : GMap w64 Progress) (y : w64) (o : List Msg), ⌜y ∈ c.voters⌝ -∗ G' o -∗
            HookGateOpt ({ s with votes := recordVote s.votes m.From' (!m.Reject') } : NState).gh.tr r
              (sendOutGate id { campRoleState id { s with votes := recordVote s.votes m.From' (!m.Reject') }
                  (decide (campaignElection = campaignPreElection)) with prvals := pvs } c
                (if y = id then vrespW32 (decide (campaignElection = campaignPreElection))
                 else vreqW32 (decide (campaignElection = campaignPreElection)))
                [campMsg (decide (campaignElection = campaignPreElection)) id
                  (({ s with votes := recordVote s.votes m.From' (!m.Reject') } : NState).term + W64 1)
                  (plogLast ({ s with votes := recordVote s.votes m.From' (!m.Reject') } : NState).logst.prev
                    (({ s with votes := recordVote s.votes m.From' (!m.Reject') } : NState).logst.sents ++
                     ({ s with votes := recordVote s.votes m.From' (!m.Reject') } : NState).logst.uents))
                  (transferCtx campaignElection) y])
              (G' (o ++ [campMsg (decide (campaignElection = campaignPreElection)) id
                  (({ s with votes := recordVote s.votes m.From' (!m.Reject') } : NState).term + W64 1)
                  (plogLast ({ s with votes := recordVote s.votes m.From' (!m.Reject') } : NState).logst.prev
                    (({ s with votes := recordVote s.votes m.From' (!m.Reject') } : NState).logst.sents ++
                     ({ s with votes := recordVote s.votes m.From' (!m.Reject') } : NState).logst.uents))
                  (transferCtx campaignElection) y]))) $$ []
        · rw [Hde, Htc]
          imodintro
          iintro %pvs %y %o %Hy HG
          ispecialize Hgvote $$ %(⟨trivial, Hwin.2⟩) %pvs %y %o %Hy HG
          iapply hookGateOpt_congr _ _ r _ _ _ (by rfl) (by rfl) $$ Hgvote
        try rw [show go_etcd_io.raft.v3.campaignElection = #campaignElection from rfl]
        wp_apply wp_raft_campaign _ _ _ { s with votes := recordVote s.votes m.From' (!m.Reject') }
            _ (G s.outbox) G' Hnl1 Hcfg Hnw1
            (fun h => by
              have := congrArg List.length h
              simp [campaignElection, campaignPreElection] at this) Hpinv
            $$ [$Hphys $HG $Hgbc $Hgsend]
          as %peers %pvs ⟨%Hpeers, Hphys, HG⟩
        iapply HΦ $$ %GoInterface.nil %_ %false %c
        iframe Hphys
        simp only [Bool.false_eq_true, ↓reduceIte]
        isplitr [HG]
        · ipureintro
          refine Hres_pv _ true false peers pvs (fun _ => ⟨Hwon.1 rfl, Hpeers⟩)
            (fun h => absurd h (by decide)) ?_
          rw [Htc]
          rfl
        isplitr [HG]
        · ipureintro; first | rfl | trivial
        ileft
        isplitr
        · ipureintro
          rw [← HHk]
          exact Or.inr (Or.inr ⟨Or.inr ⟨Hty, Hrole⟩, Or.inl (Hwon.1 rfl)⟩)
        iidx HG
      · -- `quorum.VoteLost`: step down at the unchanged term
        simp only [VoteLost]
        wp_auto
        wp_apply raft.wp_load_TermC $$ Hphys as Hphys
        have Hlo : (m.Type' = MsgVoteResp ∧ s.role = .candidate ∨
            m.Type' = MsgPreVoteResp ∧ s.role = .preCandidate) ∧
            JLost c (recordVote s.votes m.From' (!m.Reject')) := ⟨Or.inr ⟨Hty, Hrole⟩, Hlost.1 rfl⟩
        ispecialize Hglost $$ %(by first | exact ⟨Or.inl ⟨trivial, Hrole⟩, Hlost.1 rfl⟩ | exact ⟨Or.inr ⟨trivial, Hrole⟩, Hlost.1 rfl⟩) HG
        wp_apply wp_raft_becomeFollower c r id _ _ _ (G' s.outbox) (by exact Int.le_refl _) (fun _ => rfl)
          $$ [$Hphys $Hglost] as %pvs ⟨Hphys, HG⟩
        iapply HΦ $$ %GoInterface.nil %_ %false %c
        iframe Hphys
        simp only [Bool.false_eq_true, ↓reduceIte]
        isplitr [HG]
        · ipureintro
          exact Hres_pv _ false true [] pvs (fun h => absurd h (by decide)) (fun _ => Hlost.1 rfl) rfl
        isplitr [HG]
        · ipureintro; first | rfl | trivial
        ileft
        isplitr
        · ipureintro
          rw [← HHk]
          exact Or.inr (Or.inr ⟨Or.inr ⟨Hty, Hrole⟩, Or.inr (Hlost.1 rfl)⟩)
        iidx HG
      · -- `quorum.VotePending`: keep waiting
        simp only [VotePending]
        wp_auto
        iapply HΦ $$ %GoInterface.nil %_ %false %c
        iframe Hphys
        simp only [Bool.false_eq_true, ↓reduceIte]
        isplitr [HG]
        · ipureintro
          refine Hres_pv _ false false [] s.prvals (fun h => absurd h (by decide))
            (fun h => absurd h (by decide)) ?_
          cases s; rfl
        isplitr [HG]
        · ipureintro; first | rfl | trivial
        iright
        isplitr
        · ipureintro
          rw [← HHk]
          refine Hnot _ Hna Hnh ?_
          rintro ⟨_, h | h⟩
          · exact absurd (Hwon.2 h) (by decide)
          · exact absurd (Hlost.2 h) (by decide)
        iidx HG

  · -- `MsgReadIndex`, `MsgReadIndexResp` (2026-10-12), and (2026-10-13) `MsgForgetLeader`,
    -- `MsgTransferLeader` and the local reports: no arm; `MsgTimeoutNow`: logged. In each case
    -- `myVoteRespType` is one of the two vote response types, neither of these
    have Hnh0 : ¬ (m.Type' = MsgApp ∨ m.Type' = MsgHeartbeat ∨
        ((m.Type' = MsgVoteResp ∧ s.role = .candidate ∨
          m.Type' = MsgPreVoteResp ∧ s.role = .preCandidate) ∧
         (JQuorum c (granted (recordVote s.votes m.From' (!m.Reject'))) ∨
          JLost c (recordVote s.votes m.From' (!m.Reject'))))) := by
      rcases Hty with Hty' | Hty' | Hty' | Hty' | Hty' | Hty' | Hty' <;> rw [Hty'] <;>
        simp [MsgReadIndex, MsgReadIndexResp, MsgForgetLeader, MsgTransferLeader,
          MsgTimeoutNow, MsgUnreachable, MsgSnapStatus, MsgApp, MsgHeartbeat, MsgVoteResp, MsgPreVoteResp]
    rcases Hty with Hty' | Hty' | Hty' | Hty' | Hty' | Hty' | Hty' <;> rw [Hty'] <;>
      simp only [MsgReadIndex, MsgReadIndexResp, MsgForgetLeader, MsgTransferLeader,
        MsgTimeoutNow, MsgUnreachable, MsgSnapStatus] <;> wp_auto
    all_goals
      by_cases Hp : s.role = .preCandidate
      · rw [Hmp Hp]
        wp_auto
        try (
          wp_apply raft.wp_load_idC $$ Hphys as Hphys
          wp_apply raft.wp_load_TermC $$ Hphys as Hphys
          wp_apply raft.wp_load_stateC $$ Hphys as Hphys
          wp_apply wp_GetFrom.1 ml _ _ _ _ $$ [$Hm] as Hm
          wp_raft_logC)
        iapply HΦ $$ %GoInterface.nil %s %false %c
        iframe Hphys
        simp only [Bool.false_eq_true, ↓reduceIte]
        isplitr [HG]
        · ipureintro
          unfold CandidateStepResultC
          refine ⟨by simp [Hty', MsgSnap, MsgReadIndex, MsgReadIndexResp, MsgForgetLeader, MsgTransferLeader, MsgTimeoutNow, MsgUnreachable, MsgSnapStatus], ?_⟩
          simp [Hty', MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
            MsgAppResp, MsgHeartbeatResp, MsgCheckQuorum, MsgSnap, MsgPreVoteResp, MsgReadIndex, MsgReadIndexResp,
            MsgForgetLeader, MsgTransferLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow]
        isplitr [HG]
        · ipureintro; first | rfl | trivial
        iright
        isplitr
        · ipureintro
          rw [← HHk]
          exact Hnh0
        iidx HG
      · rw [Hmc Hp]
        wp_auto
        try (
          wp_apply raft.wp_load_idC $$ Hphys as Hphys
          wp_apply raft.wp_load_TermC $$ Hphys as Hphys
          wp_apply raft.wp_load_stateC $$ Hphys as Hphys
          wp_apply wp_GetFrom.1 ml _ _ _ _ $$ [$Hm] as Hm
          wp_raft_logC)
        iapply HΦ $$ %GoInterface.nil %s %false %c
        iframe Hphys
        simp only [Bool.false_eq_true, ↓reduceIte]
        isplitr [HG]
        · ipureintro
          unfold CandidateStepResultC
          refine ⟨by simp [Hty', MsgSnap, MsgReadIndex, MsgReadIndexResp, MsgForgetLeader, MsgTransferLeader, MsgTimeoutNow, MsgUnreachable, MsgSnapStatus], ?_⟩
          simp [Hty', MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
            MsgAppResp, MsgHeartbeatResp, MsgCheckQuorum, MsgSnap, MsgPreVoteResp, MsgReadIndex, MsgReadIndexResp,
            MsgForgetLeader, MsgTransferLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow]
        isplitr [HG]
        · ipureintro; first | rfl | trivial
        iright
        isplitr
        · ipureintro
          rw [← HHk]
          exact Hnh0
        iidx HG
end proof

end EtcdGrove
end Perennial
