/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgPreVoteResp_eq.v.

One term case of `Step`'s `MsgPreVoteResp` branch (2026-10-04): the incoming term is
the node's own. In its own file so that it checks in parallel with the others;
`MsgPreVoteResp.lean` combines them. Proof structure, not specification: no
`Module Type`, no `Parameter`; only files in this directory may import it.

Lean notes:
* The branch lemma takes the callee specs (Rocq's functor argument
  `P : STEP_POSTULATES`) as its first argument `_P : raft.Step.Postulates`, and Rocq's
  section variable `c` as its second.
* Rocq's `Local Ltac`s `recv_elem` (membership in a `recv` list built from `++` and
  singletons), `wp_load_step` (`raft.wp_load_stepC` on `"Hphys"`) and `ne_ty`
  (`bool_decide (m.Type = c) = false` by `w32_ne`) are not ported. The four role
  cases of `r.step(m)` (shared by `MsgPreVoteResp_gt.lean` and `MsgPreVoteResp_eq.lean`)
  are the local macro `prevote_resp_dispatch`.

raft v3.7 (2026-10-15, stage R4 phase 3): the message is a pointer `ml` with `msgIn ml □ ⟨m, ents,
sn, ctx, rs⟩`, read by its getters (`wp_get`/`wp_gets`, `ElectionLemmas.lean`, by `PB`; `Step`
first checks `m != nil`, `msgPtsC_nn`) and handed to `r.step` whole (the `stepX` specs take
`msgIn`; their `MsgSnap` premise is pure). The callees now see the message's entries and context
(the old proof passed `[]`), so the pre-vote lemmas are restated here at any `cl`/`ctx`
(`followerStepResult_prevoteresp'` etc., private; the proofs are `prevote_lemmas.lean`'s).
-/
module

public import Raft37.Proof.go_etcd_io.raft.v3.raft__Step.prevote_lemmas
public import Raft37.Proof.go_etcd_io.raft.v3.raft__Step.ElectionLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section branches
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

namespace StepProof

/-! The pre-vote lemmas (`prevote_lemmas.lean`) at any context `cl` (stage R4: the callees now
see the message's context; the old proof passed `[]`). -/

/-- Unfold the message-type constants and decide the equalities between them (the
`case_decide … w32_ne` chains of the Rocq proofs). -/
local macro "mtype_simp" : tactic =>
  `(tactic| simp (config := { decide := true }) only [Perennial.EtcdGrove.MsgBeat,
      Perennial.EtcdGrove.MsgHup, Perennial.EtcdGrove.MsgProp, Perennial.EtcdGrove.MsgApp,
      Perennial.EtcdGrove.MsgAppResp, Perennial.EtcdGrove.MsgVote,
      Perennial.EtcdGrove.MsgVoteResp, Perennial.EtcdGrove.MsgSnap,
      Perennial.EtcdGrove.MsgHeartbeat, Perennial.EtcdGrove.MsgHeartbeatResp,
      Perennial.EtcdGrove.MsgPreVote, Perennial.EtcdGrove.MsgPreVoteResp,
      or_false, false_or, false_and, and_false, ↓reduceIte, Bool.false_eq_true] at *)

/-- `stepFollower` has no `MsgPreVoteResp` arm. -/
private theorem followerStepResult_prevoteresp' (c : CfgM) {scfg : CSLists} {c' : CfgM} (id : w64) (s : NState) (m : MessageM)
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
private theorem leaderStepResult_prevoteresp' (c : CfgM) (id : w64) (s : NState)
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
  rcases Hres with ⟨-, Hres⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨Hc6, -⟩
  rotate_right
  · exfalso
    rcases Hc6 with h6 | h6 | h6 | h6 | h6 <;> exact absurd h6 (by w32_ne)
  · exact Hres
  all_goals exact absurd Hc (by w32_ne)

/-- `stepCandidate` on a `MsgPreVoteResp`: nothing at a candidate; at a pre-candidate,
the tally and then win / lose / wait, which is `stepC_prevoteRespResult`. -/
private theorem candidateStepResult_prevoteresp' (c : CfgM) {scfg : CSLists} {c' : CfgM} (id : w64) (s : NState)
    (m : MessageM) (ents : List EntryM) (sv : SnapshotM) (dropped : Bool)
    (s' : NState) (cl : List w8) :
    m.Type' = MsgPreVoteResp →
    (s.role = .candidate ∨ s.role = .preCandidate) →
    id ∈ c.voters →
    (s.role = .preCandidate → uint.Z s.term + 1 < 2 ^ 64) →
    NStateWf s →
    CandidateStepResultC c scfg id s m ents sv dropped s' c' cl →
    c = c' ∧ dropped = false ∧ NStateWf s' ∧ StepCD c id m s [] s' ∧
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
    exact StepCD.of_excluded (stepC_prevoteRespResult c id s _ _ won lost peers pvs Hp Hin (Hnw Hp)
      (fun Hwon => (Hw Hwon).2)) (.inr Hp)
  · simp only [Hp, ↓reduceIte] at Hres
    subst Hres
    exact ⟨Hwf, StepCD.frame (.refl _) (RFrame.refl _), RespStep.refl _ _,
      keep_frame rfl rfl rfl rfl rfl⟩

set_option hygiene false in
/-- `r.step(m)` on a `MsgPreVoteResp` at the node's own term, by role (Rocq: the four
role cases, each with `wp_load_step`): `stepFollower` and `stepLeader` have no arm for
it; `stepCandidate` ignores it at a candidate and tallies it at a pre-candidate
(`candidateStepResult_prevoteresp`). Consumes nothing. Uses `Hphys`, `HΦ`, `Hty`,
`Hwf`, `Hcfg`, `Hnw`. -/
local macro "prevote_resp_dispatch" : tactic =>
  `(tactic| (
    wp_gets
    wp_apply Perennial.EtcdGrove.raft.wp_load_stepC $$ Hphys as Hphys
    icases Perennial.EtcdGrove.ownRaftPhysC_voter c r id s $$ Hphys with ⟨%Hvoter, Hphys⟩
    rw [show s.stepfn = stepFuncOf s.role from Hwf.1]
    -- (stage R4) the message as the callees take it: read-only entries (not a proposal)
    have Hnp : ¬ m.Type' = MsgProp := by rw [Hty]; w32_ne
    cases Hrole : s.role
    · -- Follower: no arm
      simp only [stepFuncOf]
      wp_apply _P.stepFollower c ∅ r id s ml m ents sn rs (zero_val _) ctx
          (.inr (.inr (.inr (.inr (.inr (.inr (.inl Hty)))))))
          (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
          (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
          (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
          (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
          (fun Hc => by exfalso; rcases Hc with Hc | Hc <;> rw [Hty] at Hc <;> exact absurd Hc (by w32_ne))
          (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        $$ [Hphys Hm] as %err %s1 %dropped %c1 ⟨Hphys, %Hres, Herrn⟩
      · iframe Hphys; rw [ite_eq_right Hnp]; iexact Hm
      obtain ⟨rfl, rfl, rfl⟩ := followerStepResult_prevoteresp' _ _ _ _ _ _ _ _ _ Hty Hres
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Herrn with %Herrn
      subst Herrn
      try wp_auto
      iapply HΦ $$ %interface.nil %_
      iframe Hphys
      ipureintro
      exact ⟨Hwf, ⟨[], fun _ h => absurd h List.not_mem_nil, StepCD.frame (.refl _) (RFrame.refl _)⟩, rfl,
      RespStep.refl _ _, keep_frame rfl rfl rfl rfl rfl⟩
    · -- Candidate: `myVoteRespType` is `MsgVoteResp`; a stale pre-vote response is
      -- ignored
      simp only [stepFuncOf]
      wp_apply _P.stepCandidate c ∅ r id s ml m ents sn rs (zero_val _) ctx
          (.inr (.inr (.inr (.inr (.inr (.inr (.inl Hty)))))))
          (fun Hc => by
            exfalso; rw [Hty] at Hc
            rcases Hc with Hc | Hc | Hc | Hc <;> exact absurd Hc (by w32_ne))
          (.inl Hrole)
          (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
          (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
          (fun Hp _ => Hnw Hp)
          (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        $$ [Hphys Hm] as %err %s1 %dropped %c1 ⟨Hphys, %Hres, Herrn⟩
      · iframe Hphys; rw [ite_eq_right Hnp]; iexact Hm
      obtain ⟨rfl, rfl, Hwf1, Hst, Hresp, Hft⟩ :=
        candidateStepResult_prevoteresp' c _ _ _ _ _ _ _ _ Hty (.inl Hrole)
          (Hvoter (by rw [Hrole]; decide)) Hnw Hwf Hres
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Herrn with %Herrn
      subst Herrn
      try wp_auto
      iapply HΦ $$ %interface.nil %s1
      iframe Hphys
      ipureintro
      exact ⟨Hwf1, ⟨[], fun _ h => absurd h List.not_mem_nil, Hst⟩, rfl, Hresp, Hft⟩
    · -- Leader: no arm
      simp only [stepFuncOf]
      wp_apply _P.stepLeader c r id s ml m ents sn ctx rs
          (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl Hty))))))))
          Hrole
          (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
          (fun Hc => by
            exfalso; rw [Hty] at Hc
            rcases Hc with Hc | ⟨Hc, -⟩ <;> exact absurd Hc (by w32_ne))
          (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
          (fun Hc => by exfalso; rw [Hty] at Hc; rcases Hc with Hc | Hc | Hc <;> exact absurd Hc (by w32_ne))
          (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
          (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        $$ [Hphys Hm] as %err %s' %dropped ⟨Hphys, %Hres, Herrn⟩
      · iframe Hphys
        isplitl [Hm]
        · rw [ite_eq_right Hnp]; iexact Hm
        · iintro %Hc; exfalso; exact Hnp Hc
      obtain ⟨rfl, rfl⟩ := leaderStepResult_prevoteresp' c _ _ _ _ _ _ _ Hty Hres
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Herrn with %Herrn
      subst Herrn
      try wp_auto
      iapply HΦ $$ %interface.nil %_
      iframe Hphys
      ipureintro
      exact ⟨Hwf, ⟨[], fun _ h => absurd h List.not_mem_nil, StepCD.frame (.refl _) (RFrame.refl _)⟩, rfl,
      RespStep.refl _ _, keep_frame rfl rfl rfl rfl rfl⟩
    · -- PreCandidate: the pre-vote tally
      simp only [stepFuncOf]
      wp_apply _P.stepCandidate c ∅ r id s ml m ents sn rs (zero_val _) ctx
          (.inr (.inr (.inr (.inr (.inr (.inr (.inl Hty)))))))
          (fun Hc => by
            exfalso; rw [Hty] at Hc
            rcases Hc with Hc | Hc | Hc | Hc <;> exact absurd Hc (by w32_ne))
          (.inr Hrole)
          (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
          (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
          (fun Hp _ => Hnw Hp)
          (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        $$ [Hphys Hm] as %err %s1 %dropped %c1 ⟨Hphys, %Hres, Herrn⟩
      · iframe Hphys; rw [ite_eq_right Hnp]; iexact Hm
      obtain ⟨rfl, rfl, Hwf1, Hst, Hresp, Hft⟩ :=
        candidateStepResult_prevoteresp' c _ _ _ _ _ _ _ _ Hty (.inr Hrole)
          (Hvoter (by rw [Hrole]; decide)) Hnw Hwf Hres
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Herrn with %Herrn
      subst Herrn
      try wp_auto
      iapply HΦ $$ %interface.nil %s1
      iframe Hphys
      ipureintro
      exact ⟨Hwf1, ⟨[], fun _ h => absurd h List.not_mem_nil, Hst⟩, rfl, Hresp, Hft⟩))

set_option maxHeartbeats 2000000 in
/-- `MsgPreVoteResp` at `m.Term = r.Term`: the preamble does nothing and the type
switch's default arm runs `r.step(m)`. Only a pre-candidate acts on it (`stepCandidate`
with `myVoteRespType = MsgPreVoteResp`: the tally, then `campaign(campaignElection)` on
a win, `becomeFollower` on a loss); everyone else ignores it. Nothing is received by
the protocol: `StepC.refl`, `StepC.abandon` or `StepC.campaign`
(`stepC_prevoteRespResult`). -/
theorem wp_Step_MsgPreVoteResp_eq (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (PB : raft.Step.PbPostulates (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc) :
    m.Type' = MsgPreVoteResp →
    m.To' = id →
    m.Term' ≠ W64 0 →
    -- this file: the same term
    m.Term' = s.term →
    (s.role = .preCandidate → uint.Z s.term + 1 < 2 ^ 64) →
    NStateWf s →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
        "Hm" ∷ msgIn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absMsg .preVoteResp m ents) ∧
            StepCD c id m s recv s'⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hresp" ∷ ⌜RespStep m s s'⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ }} := by
  intro Hty Hto Hterm Hteq Hnw Hwf
  wp_start as ⟨Hphys, Hm⟩
  icases msgPtsC_nn _ _ _ _ _ $$ Hm with ⟨%Hnn, Hm⟩
  try wp_auto
  wp_gets
  rw [decide_eq_false Hnn]
  try wp_auto
  wp_gets
  wp_apply _P.traceReceiveMessage
  try wp_auto
  wp_gets
  -- `m.Term ≠ 0`, so the first arm of the term preamble is skipped
  wp_gets
  rw [decide_eq_false Hterm]
  try wp_auto
  wp_gets
  wp_apply raft.wp_load_TermC $$ Hphys as Hphys
  wp_gets
  rw [decide_eq_false (show ¬ uint.Z s.term < uint.Z m.Term' by rw [Hteq]; omega)]
  try wp_auto
  wp_gets
  wp_apply raft.wp_load_TermC $$ Hphys as Hphys
  wp_gets
  rw [decide_eq_false (show ¬ uint.Z m.Term' < uint.Z s.term by rw [Hteq]; omega)]
  try wp_auto
  -- the type switch: none of its four cases, so `r.step(m)`
  wp_gets
  rw [Hty]
  try wp_auto
  prevote_resp_dispatch

end StepProof

end branches

end EtcdGrove
end Perennial
