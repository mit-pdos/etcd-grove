/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_prevote_lemmas.v.

Pure lemmas shared by `Step`'s pre-vote branches (`proof_raft__Step_MsgPreVote*.v`,
`proof_raft__Step_MsgPreVoteResp*.v`), 2026-10-04.

Proof structure, not specification: no `Module Type`, no `Parameter`, no Hoare triple.
Each lemma takes a `stepX` result relation apart for `MsgPreVoteResp`, outside any WP,
where the `decide` chains are cheap. Only files in this directory may `Require` it.

Lean notes: Rocq's section variable `c` is an explicit first argument of every lemma
that uses it. Rocq's `case_decide … w32_ne` chains are the macro `mtype_simp`
(unfold the message-type constants, decide the equalities between them).
-/
module

public import Proof.go_etcd_io.raft.v3.raft__Step.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section prevote
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

namespace StepProof

/-- Unfold the message-type constants and decide the equalities between them (the
`case_decide … w32_ne` chains of the Rocq proofs). -/
macro "mtype_simp" : tactic =>
  `(tactic| simp (config := { decide := true }) only [Perennial.EtcdGrove.MsgBeat,
      Perennial.EtcdGrove.MsgHup, Perennial.EtcdGrove.MsgProp, Perennial.EtcdGrove.MsgApp,
      Perennial.EtcdGrove.MsgAppResp, Perennial.EtcdGrove.MsgVote,
      Perennial.EtcdGrove.MsgVoteResp, Perennial.EtcdGrove.MsgSnap,
      Perennial.EtcdGrove.MsgHeartbeat, Perennial.EtcdGrove.MsgHeartbeatResp,MsgCheckQuorum,
      Perennial.EtcdGrove.MsgPreVote, Perennial.EtcdGrove.MsgPreVoteResp,
      or_false, false_or, false_and, and_false, ↓reduceIte, Bool.false_eq_true] at *)

/-- `stepFollower` has no `MsgPreVoteResp` arm. -/
theorem followerStepResult_prevoteresp (c : CfgM) {scfg : CSLists} {c' : CfgM} (id : w64) (s : NState) (m : MessageM)
    (ents : List EntryM) (sv : SnapshotM) (dropped : Bool) (s' : NState) (cl : List w8) :
    m.Type' = MsgPreVoteResp →
    FollowerStepResultC c scfg id s m ents sv dropped s' c' cl → c = c' ∧ dropped = false ∧ s' = s := by
  intro Hty H
  unfold FollowerStepResultC at H
  refine ⟨(FollowerStepResultC.cfg (by nonsnap Hty) H).symm, ?_⟩
  replace H := H.2
  rw [Hty] at H
  mtype_simp
  exact H

/-- `stepLeader` has none either. -/
theorem leaderStepResult_prevoteresp (c : CfgM) (id : w64) (s : NState)
    (m : MessageM) (ents : List EntryM) (dropped : Bool) (s' : NState) (ctx : List w8) :
    m.Type' = MsgPreVoteResp →
    LeaderStepResultC c id s m ents dropped s' ctx → dropped = false ∧ s' = s := by
  intro Hty H
  unfold LeaderStepResultC at H
  rw [Hty] at H
  mtype_simp
  obtain ⟨rfl, Hres⟩ := H
  refine ⟨rfl, ?_⟩
  unfold LeaderNonpropResultC at Hres
  rw [Hty] at Hres
  rcases Hres with ⟨-, Hres⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨Hc6, -⟩ | ⟨Hc7, -⟩
  rotate_right
  · exfalso; first | (rw [Hty] at Hc7; exact absurd Hc7 (by w32_ne)) | (rcases Hty with h' | h' <;> rw [h'] at Hc7 <;> exact absurd Hc7 (by w32_ne)) | exact absurd Hc7 (by w32_ne)
  rotate_right
  · exfalso
    rcases Hc6 with h6 | h6 | h6 | h6 | h6 <;> exact absurd h6 (by w32_ne)
  · exact Hres
  all_goals exact absurd Hc (by w32_ne)

/-- A pre-candidate's tally keeps the log, and the term or moves it one up (a win's
`campaign`). -/
theorem prevoteRespResult_frame (id : w64) (s : NState) (src : w64) (reject won lost : Bool)
    (peers : List w64) (pvs : GMap w64 Progress) (m : MessageM)
    (Hty : m.Type' = MsgPreVoteResp) (Hnw : uint.Z s.term + 1 < 2 ^ 64) :
    NetFrame s { prevoteRespResult id s src reject won lost peers with prvals := pvs } ∧
    TermStep m s { prevoteRespResult id s src reject won lost peers with prvals := pvs } := by
  have H : ({ prevoteRespResult id s src reject won lost peers with prvals := pvs } :
        NState).logst = s.logst ∧
      uint.Z s.term ≤
        uint.Z ({ prevoteRespResult id s src reject won lost peers with prvals := pvs } :
          NState).term ∧
      ({ prevoteRespResult id s src reject won lost peers with prvals := pvs } :
          NState).prevote = s.prevote ∧
      ({ prevoteRespResult id s src reject won lost peers with prvals := pvs } :
          NState).gh = s.gh := by
    unfold prevoteRespResult
    split
    · refine ⟨rfl, ?_, rfl, rfl⟩
      simp only [campaignState, sendMsgs, becomeCandidate, resetTo, resetTo0, Bool.false_eq_true,
        ↓reduceIte]
      word
    · split
      · exact ⟨rfl, Int.le_refl _, rfl, rfl⟩
      · exact ⟨rfl, Int.le_refl _, rfl, rfl⟩
  obtain ⟨Hl, Ht, Hpv, Hg⟩ := H
  refine ⟨NetFrame.of_logst Hl Hpv Hg, Ht, fun h => ?_, fun _ h => absurd Hty h,
    fun _ => by rw [Hl]; exact Int.le_refl _, fun h => ?_, fun h => ?_⟩
  · rw [Hty] at h; exact absurd h (by w32_ne)
  · rw [Hty] at h; exact absurd h (by w32_ne)
  · -- (2026-10-17) a pre-candidate afterwards stayed one, at its term
    unfold prevoteRespResult at h ⊢
    split at h
    · simp [campaignState, sendMsgs, becomeCandidate] at h
    · split at h <;> simp_all [becomeFollower, PreKeep]

/-- A pre-candidate's tally, for `RespStep`: a win campaigns -- a candidate one term up
(the term does not wrap) -- a loss steps down at the same term, and otherwise it stays a
pre-candidate at the same term. -/
theorem prevoteRespResult_resp (id : w64) (s : NState) (src : w64) (reject won lost : Bool)
    (peers : List w64) (pvs : GMap w64 Progress) (m : MessageM)
    (Hty : m.Type' = MsgPreVoteResp) (Hp : s.role = .preCandidate)
    (Hnw : uint.Z s.term + 1 < 2 ^ 64) :
    RespStep m s { prevoteRespResult id s src reject won lost peers with prvals := pvs } := by
  refine ⟨fun h => by rcases h with h | h <;> rw [Hty] at h <;> exact absurd h (by w32_ne),
    fun _ => ?_⟩
  unfold prevoteRespResult
  split
  · refine ⟨.inr ⟨Hp, ?_⟩, fun h => ?_⟩
    · simp only [campaignState, sendMsgs, becomeCandidate, resetTo, resetTo0, Bool.false_eq_true,
        ↓reduceIte]
      word
    · simp [campaignState, sendMsgs, becomeCandidate] at h
  · split
    · refine ⟨.inl (Int.le_max_left _ _), fun h => ?_⟩
      simp [becomeFollower] at h
    · exact ⟨.inl (Int.le_max_left _ _), fun _ => ⟨Hp, rfl⟩⟩

/-- (2026-10-25, T-M M2b) A pre-candidate's tally in the dynamic model: waiting is no step, a loss
`abandon`, a win `StepR.campaign`, whose guard is the pre-candidate's (`PreGuard`: `hup` checked
it, and nothing since changed the log, the commit index or the pending snapshot). Until then the
dynamic mode had no pre-candidate (`StepCD.of_excluded`). -/
theorem stepR_prevoteRespResult {Adm : List EntryM → CCState → Prop} {dec : CCDec} (c : CfgM)
    (id : w64) (s : NState) (src : w64) (reject won lost : Bool) (peers : List w64)
    (pvs : GMap w64 Progress) (Hpre : s.role = .preCandidate) (Hin : id ∈ c.voters)
    (Hnw : uint.Z s.term + 1 < 2 ^ 64)
    (Hperm : won = true → peers ≡ₚ elements (c.voters \ {[id]})) (g : RGh) (hc : g.cfg.cfg = c)
    (Hg : s.logst.snap = none ∧ NoConfIn (g.fp ++ (s.logst.sents ++ s.logst.uents))
      (uint.nat s.logst.applied) (uint.nat s.logst.committed)) :
    StepR Adm dec id B (rOf s g) []
      (rOf { prevoteRespResult id s src reject won lost peers with prvals := pvs } g) := by
  have Hnl : s.role ≠ .leader := by rw [Hpre]; decide
  have Hnl' : (rOf s g).p.role ≠ .leader := by
    simp only [rOf, toPState_role]; exact proleRole_not_leader _ Hnl
  obtain ⟨Hsn, Hno⟩ := Hg
  cases won <;> cases lost
  · -- waiting: the tally only, which the model does not see at a pre-candidate
    have e : rOf { prevoteRespResult id s src reject false false peers with prvals := pvs } g =
        rOf s g := by
      have h1 : toPState { prevoteRespResult id s src reject false false peers with prvals := pvs } =
          toPState s := by
        simp [prevoteRespResult, toPState, Hpre]
      unfold rOf pciR
      rw [h1]
      simp [prevoteRespResult, Hpre]
    rw [e]; exact .refl _
  · -- a loss: `abandon`
    have Hbf : (becomeFollower s s.term (W64 0)).role ≠ .leader := by simp [becomeFollower]
    show StepR Adm dec id B (rOf s g) [] (rOf { becomeFollower s s.term (W64 0) with prvals := pvs } g)
    rw [rOf_nonleader s ({ becomeFollower s s.term (W64 0) with prvals := pvs } : NState) g rfl rfl
      (by exact Hbf), toPState_prvals_nl _ pvs Hbf, toPState_becomeFollower]
    have H := (StepCF.abandon (c := c) (id := id) _ Hnl').toR (Adm := Adm) (dec := dec) (B := B)
      (rOf s g) rfl hc (rOf_pci_zero s g)
    have e : pciKeep (pbecomeFollower (rOf s g).p (rOf s g).p.term (W64 0)) (rOf s g).pci = W64 0 := by
      simp [pciKeep, pbecomeFollower]
    rw [e] at H
    exact H
  all_goals
    -- a win: the campaign, with the guard `hup` checked
    have Hcr : (campaignState id s false peers).role ≠ .leader := by
      simp [campaignState, sendMsgs, becomeCandidate]
    have Hcl : (campaignState id s false peers).logst = s.logst := by
      simp [campaignState, sendMsgs, becomeCandidate, resetTo, resetTo0]
    show StepR Adm dec id B (rOf s g) [] (rOf { campaignState id s false peers with prvals := pvs } g)
    rw [rOf_nonleader s ({ campaignState id s false peers with prvals := pvs } : NState) g
      (by show (campaignState id s false peers).logst.applied = _; rw [Hcl])
      (by show (campaignState id s false peers).logst.snap = _; rw [Hcl]) (by exact Hcr),
      toPState_prvals_nl _ pvs Hcr]
    show StepR Adm dec id B (rOf s g) []
      { rOf s g with p := toPState (sendMsgs (becomeCandidate id s) _), pci := W64 0 }
    rw [toPState_sendMsgs, toPState_becomeCandidate]
    exact StepR.campaign (rOf s g) peers [] Hnl' (by show id ∈ g.cfg.cfg.voters; rw [hc]; exact Hin)
      (by simp [rOf, Hsn]) Hno Hnw (by show peers ≡ₚ elements (g.cfg.cfg.voters \ {[id]}); rw [hc]; exact Hperm rfl)

/-- `stepCandidate` on a `MsgPreVoteResp`: nothing at a candidate; at a pre-candidate,
the tally and then win / lose / wait, which is `stepC_prevoteRespResult`. -/
theorem candidateStepResult_prevoteresp (c : CfgM) {scfg : CSLists} {c' : CfgM} (id : w64) (s : NState)
    (m : MessageM) (ents : List EntryM) (sv : SnapshotM) (dropped : Bool)
    (s' : NState) (cl : List w8) :
    m.Type' = MsgPreVoteResp →
    (s.role = .candidate ∨ s.role = .preCandidate) →
    id ∈ c.voters →
    (s.role = .preCandidate → uint.Z s.term + 1 < 2 ^ 64) →
    NStateWf s →
    CandidateStepResultC c scfg id s m ents sv dropped s' c' cl →
    c = c' ∧ dropped = false ∧ NStateWf s' ∧ StepCD c id B m s [] s' ∧
      RespStep m s s' ∧ NetFrame s s' ∧ TermStep m s s' := by
  intro Hty Hrole Hin Hnw Hwf H
  unfold CandidateStepResultC at H
  refine ⟨(CandidateStepResultC.cfg (by nonsnap Hty) H).symm, ?_⟩
  replace H := H.2
  rw [Hty] at H
  mtype_simp
  obtain ⟨rfl, Hres⟩ := H
  refine ⟨rfl, ?_⟩
  by_cases Hp : s.role = .preCandidate
  · simp only [Hp, ↓reduceIte] at Hres
    obtain ⟨won, lost, peers, pvs, Hw, -, rfl⟩ := Hres
    refine ⟨nstateWf_prvals _ _ (nstateWf_prevoteRespResult _ _ _ _ _ _ _ Hwf), ?_,
      prevoteRespResult_resp id s _ _ won lost peers pvs m Hty Hp (Hnw Hp),
      prevoteRespResult_frame id s _ _ won lost peers pvs m Hty (Hnw Hp)⟩
    exact ⟨stepC_prevoteRespResult c id s _ _ won lost peers pvs Hp Hin (Hnw Hp)
      (fun Hwon => (Hw Hwon).2), fun Adm dec g hc hd => ⟨g.cidx, .inl rfl,
        stepR_prevoteRespResult c id s _ _ won lost peers pvs Hp Hin (Hnw Hp)
          (fun Hwon => (Hw Hwon).2) g hc (hd.2.1 Hp)⟩⟩
  · simp only [Hp, ↓reduceIte] at Hres
    subst Hres
    exact ⟨Hwf, StepCD.frame (.refl _) (RFrame.refl _), RespStep.refl _ _,
      keep_frame rfl rfl rfl rfl rfl⟩

end StepProof

end prevote

end EtcdGrove
end Perennial
