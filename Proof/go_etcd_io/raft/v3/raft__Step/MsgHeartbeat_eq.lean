/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgHeartbeat_eq.v.

One term case of `Step`'s `MsgHeartbeat` branch (the current term: `r.step(m)`, by
role), in its own file so that it checks in parallel with the others;
`proof_raft__Step_MsgHeartbeat.v` combines them. Proof structure, not specification: no
`Module Type`, no `Parameter`; only files in this directory may `Require` it.

Lean notes:
* The branch lemma takes the callee specs (Rocq's functor argument
  `P : STEP_POSTULATES`) as its first argument `_P : raft.Step.Postulates`, and Rocq's
  section variable `c` as its second.
* Rocq's `Local Ltac`s `recv_elem` (closing `∀ m' ∈ recv, m' = …` goals: `elem_of_app`,
  `list_elem_of_singleton`, `elem_of_nil`, `naive_solver`) and `wp_load_step` (the load
  of `r.step` in `r.step(r, m)`, bound by hand with `raft.wp_load_stepC`, as `wp_apply`
  does not find a load in function position) are not ported.
-/
module

public import Proof.go_etcd_io.raft.v3.raft__Step.repl_lemmas
public import Proof.go_etcd_io.raft.v3.raft__Step.ReplLemmas

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

set_option maxHeartbeats 1000000 in
theorem wp_Step_MsgHeartbeat_eq (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (_Q : raft.Step.ReplPbPostulates (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc)
    (ents : List EntryM) :
    m.Type' = MsgHeartbeat →
    m.To' = id →
    m.Term' ≠ W64 0 →
    m.From' ≠ W64 0 →
    m.From' ≠ id →
    NStateWf s →
    -- protocol fact (`heartbeat_commit_le_last`)
    uint.Z m.Commit' ≤ plogLastIndexZ s.logst.prev (s.logst.sents ++ s.logst.uents) →
    -- this file: the current term: `r.step(m)`, by role
    m.Term' = s.term →
    -- a follower's vote tally is empty (`padoptLeader` clears it, and `NStateWf` does
    -- not say so); see the combining file
    (s.role = .follower → s.votes = ∅) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
        "Hm" ∷ msgIn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absMsg .heartbeat m ents ctx) ∧
            StepCD c id m s recv s'⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ }} := by
  intro Hty Hto Hterm Hfnz Hfid Hwf Hcommit Hteq Hvotes
  wp_start as H
  iNamed H
  icases msgPtsC_nn _ _ _ _ _ $$ Hm with ⟨%Hnn, Hm⟩
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply _P.traceReceiveMessage
  try wp_auto
  wp_get _Q
  rw [decide_eq_false Hterm]
  wp_auto
  wp_drive _Q
  rw [decide_eq_false (show ¬ uint.Z s.term < uint.Z m.Term' by rw [Hteq]; omega)]
  wp_auto
  wp_drive _Q
  rw [decide_eq_false (show ¬ uint.Z m.Term' < uint.Z s.term by rw [Hteq]; omega)]
  wp_auto
  -- the type switch: none of its cases, so `r.step(m)`
  wp_drive _Q
  wp_apply raft.wp_load_stepC $$ Hphys as Hphys
  rw [show s.stepfn = stepFuncOf s.role from Hwf.1]
  cases Hrole : s.role
  · -- Follower: `stepFollower`'s arm, with `r.lead = m.From`
    simp only [stepFuncOf]
    have Hvs := Hvotes Hrole
    wp_apply _P.stepFollower c ∅ r id s ml m ents sn rs (zero_val _) ctx (.inr (.inr (.inr (.inl Hty))))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun _ => ⟨Hcommit, Hfid⟩)
        (fun Hc => by exfalso; rcases Hc with Hc | Hc <;> rw [Hty] at Hc <;> exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      $$ [$Hphys Hm] as %err %s1 %dropped %c1 ⟨Hphys, %Hres, Herrn⟩
    · iapply msgIn_nonprop (by rw [Hty]; w32_ne) $$ Hm
    obtain ⟨rfl, rfl, rfl⟩ := followerStepResult_heartbeat _ _ _ _ _ _ _ _ _ Hty Hres
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    iapply HΦ $$ %interface.nil %_
    iframe Hphys
    ipureintro
    refine ⟨nstateWf_heartbeatResult _ _ _ _ Hwf, ⟨[absMsg .heartbeat m ents ctx], ?_, ?_⟩, rfl,
      keep_frame rfl rfl rfl rfl rfl⟩
    · intro m' Hm'
      exact List.mem_singleton.mp Hm'
    · refine StepCD.frame ?_ (by rframe)
      exact step_handle_heartbeat c id _ _ m ents ctx (adopt_follower s m.From' Hrole Hvs) Hto Hteq
        (by simp [toPState, Hrole, proleRole]) Hcommit Hfid
  · -- Candidate: `becomeFollower(r.Term, m.From)`, then the handler
    simp only [stepFuncOf]
    wp_apply _P.stepCandidate c ∅ r id s ml m ents sn rs (zero_val _) ctx
        (.inr (.inr (.inr (.inl Hty)))) (fun _ => ⟨Hteq, Hterm⟩) (.inl Hrole)
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun _ => ⟨Hcommit, Hfid⟩)
        (fun _ Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      $$ [$Hphys Hm] as %err %s1 %dropped %c1 ⟨Hphys, %Hres, Herrn⟩
    · iapply msgIn_nonprop (by rw [Hty]; w32_ne) $$ Hm
    obtain ⟨rfl, rfl, pvs, rfl⟩ := candidateStepResult_heartbeat _ _ _ _ _ _ _ _ _ Hty Hres
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    iapply HΦ $$ %interface.nil %_
    iframe Hphys
    ipureintro
    refine ⟨nstateWf_heartbeatResult _ _ _ _ ⟨rfl, rfl⟩, ⟨[absMsg .heartbeat m ents ctx], ?_, ?_⟩, rfl,
      keep_frame rfl rfl rfl rfl rfl⟩
    · intro m' Hm'
      exact List.mem_singleton.mp Hm'
    · refine StepCD.frame ?_ (by rframe)
      exact step_handle_heartbeat c id _ _ m ents ctx (adopt_candidate s m.From' pvs (by rw [Hrole]; decide)) Hto Hteq
        (by simp [toPState, Hrole, proleRole]) Hcommit Hfid
  · -- Leader: `stepLeader` has no arm for it; nothing changes
    simp only [stepFuncOf]
    wp_apply _P.stepLeader c r id s ml m ents sn ctx rs (.inr (.inr (.inr (.inr (.inr (.inr (.inl Hty)))))))
        Hrole
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by
          exfalso; rw [Hty] at Hc
          rcases Hc with Hc | ⟨Hc, -⟩ <;> exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by exfalso; rw [Hty] at Hc; rcases Hc with Hc | Hc | Hc <;> exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      $$ [$Hphys Hm] as %err %s' %dropped ⟨Hphys, %Hres, Herrn⟩
    · isplitl [Hm]
      · iapply msgIn_nonprop (by rw [Hty]; w32_ne) $$ Hm
      · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
    obtain ⟨rfl, Hs'⟩ := leaderStepResult_app_hb _ _ _ _ _ _ _ (.inr Hty) Hres
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    iapply HΦ $$ %interface.nil %s'
    iframe Hphys
    ipureintro
    rw [Hs']
    exact ⟨Hwf, ⟨[], fun _ h => absurd h List.not_mem_nil, StepCD.frame (.refl _) (RFrame.refl _)⟩, rfl,
      keep_frame rfl rfl rfl rfl rfl⟩
  · -- PreCandidate (2026-10-04), as a candidate: `becomeFollower(r.Term, m.From)`, then
    -- the handler
    simp only [stepFuncOf]
    wp_apply _P.stepCandidate c ∅ r id s ml m ents sn rs (zero_val _) ctx
        (.inr (.inr (.inr (.inl Hty)))) (fun _ => ⟨Hteq, Hterm⟩) (.inr Hrole)
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun _ => ⟨Hcommit, Hfid⟩)
        (fun _ Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      $$ [$Hphys Hm] as %err %s1 %dropped %c1 ⟨Hphys, %Hres, Herrn⟩
    · iapply msgIn_nonprop (by rw [Hty]; w32_ne) $$ Hm
    obtain ⟨rfl, rfl, pvs, rfl⟩ := candidateStepResult_heartbeat _ _ _ _ _ _ _ _ _ Hty Hres
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    iapply HΦ $$ %interface.nil %_
    iframe Hphys
    ipureintro
    refine ⟨nstateWf_heartbeatResult _ _ _ _ ⟨rfl, rfl⟩, ⟨[absMsg .heartbeat m ents ctx], ?_, ?_⟩, rfl,
      keep_frame rfl rfl rfl rfl rfl⟩
    · intro m' Hm'
      exact List.mem_singleton.mp Hm'
    · refine StepCD.frame ?_ (by rframe)
      exact step_handle_heartbeat c id _ _ m ents ctx (adopt_candidate s m.From' pvs (by rw [Hrole]; decide)) Hto Hteq
        (by simp [toPState, Hrole, proleRole]) Hcommit Hfid

end StepProof

end branches

end EtcdGrove
end Perennial
