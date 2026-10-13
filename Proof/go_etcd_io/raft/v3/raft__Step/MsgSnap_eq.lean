/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgSnap_eq.v.

One term case of `Step`'s `MsgSnap` branch (the current term: `r.step(m)` by role), in
its own file so that it checks in parallel with the others; `MsgSnap.lean` combines
them. A leader is excluded by a premise (the dispatch refutes a second leader of the
term, `isLeader_unique`). Proof structure, not specification: no `Module Type`, no
`Parameter`; only files in this directory may import it.

Lean notes:
* The branch lemmas take the callee specs (Rocq's functor argument `P : STEP_POSTULATES`)
  as their first argument `_P : raft.Step.Postulates`, and Rocq's section variable `cfg`
  as their second.
* Rocq's `Local Ltac recv_elem` (closes `∀ m' ∈ recv, m' = a` for `recv` built from
  `[]` and `[a]`) is not ported.
* Rocq's `Local Ltac wp_load_step` (binds the load of `r.step` in function position and
  applies `raft.wp_load_step` to `"Hphys"`) is not ported.
-/
module

public import Proof.go_etcd_io.raft.v3.raft__Step.repl_lemmas

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

theorem wp_Step_MsgSnap_eq (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (sv : raftpb.Snapshot) (voters : List w64) :
    m.Type' = MsgSnap →
    m.To' = id →
    m.Term' ≠ W64 0 →
    m.From' ≠ W64 0 →
    m.From' ≠ id →
    id ∈ cfg →
    NStateWf s →
    SnapScope cfg sv voters →
    -- this file: the current term
    m.Term' = s.term →
    -- not a leader: the sender leads this term (`isLeader_unique`)
    s.role ≠ .leader →
    -- a follower's vote tally is empty (`FollowerVotesOk`)
    (s.role = .follower → s.votes = ∅) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhys cfg r id s ∗
        "#Hsv" ∷ m.Snapshot' ↦□ sv ∗
        "#Hvs" ∷ sv.Metadata'.ConfState'.Voters' ↦*□ voters }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhys cfg r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absSnap m sv voters) ∧
            Step cfg id (toPState s) recv (toPState s')⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ }} := by
  intro Hty Hto Hterm Hfnz Hfid Hcfg Hwf Hscope Hteq Hnl Hvotes
  wp_start as ⟨Hphys, #Hsv, #Hvs⟩
  wp_auto
  wp_apply _P.traceReceiveMessage
  rw [decide_eq_false Hterm]
  wp_auto
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  rw [decide_eq_false (show ¬ uint.Z s.term < uint.Z m.Term' by rw [Hteq]; omega)]
  wp_auto
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  rw [decide_eq_false (show ¬ uint.Z m.Term' < uint.Z s.term by rw [Hteq]; omega)]
  wp_auto
  -- the type switch: none of its cases, so `r.step(m)`
  repeat (rw [Hty]; wp_auto)
  wp_apply raft.wp_load_step $$ Hphys as Hphys
  rw [show s.stepfn = stepFuncOf s.role from Hwf.1]
  cases Hrole : s.role
  · -- Follower: `stepFollower`'s arm, with `r.lead = m.From`
    simp only [stepFuncOf]
    have Hvs := Hvotes Hrole
    wp_apply _P.stepFollower cfg r id s m [] sv voters []
        (.inr (.inr (.inr (.inr (.inr (.inl Hty))))))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      $$ [$Hphys] as %err %s1 %dropped ⟨Hphys, %Hres, Herrn⟩
    · isplitl []
      · iintro %Hc; exfalso; rw [Hty] at Hc
        first | (rcases Hc with Hc | Hc | Hc <;> exact absurd Hc (by w32_ne)) | exact absurd Hc (by w32_ne)
      isplitl []
      · iintro %Hc; exfalso; rw [Hty] at Hc
        rcases Hc with Hc | Hc <;> exact absurd Hc (by w32_ne)
      isplitl []
      · iintro %_
        isplitr
        · ipureintro
          exact ⟨Hscope, Hrole, Hvs, Hcfg, Hfid⟩
        · iframe Hsv Hvs
      · iintro %Hc; exfalso; rw [Hty] at Hc
        rcases Hc with Hc | Hc <;> exact absurd Hc (by w32_ne)
    obtain ⟨rfl, Hhs⟩ := followerStepResult_snap _ _ _ _ _ _ _ Hty Hres
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    iapply HΦ $$ %interface.nil %s1
    iframe Hphys
    ipureintro
    refine ⟨nstateWf_handle_snap (t := { s with lead := m.From' }) _ _ _ _ Hwf Hhs,
      ⟨[absSnap m sv voters], ?_, ?_⟩, rfl⟩
    · intro m' Hm'
      exact List.mem_singleton.mp Hm'
    · exact step_handle_snap cfg id _ _ m sv voters s1 (adopt_follower s m.From' Hrole Hvs) Hto
        Hteq (by simp [toPState, Hrole, proleRole]) Hfid Hscope Hcfg Hhs
  · -- Candidate: `becomeFollower(r.Term, m.From)`, then `handleSnapshot`
    simp only [stepFuncOf]
    wp_apply _P.stepCandidate cfg r id s m [] sv voters []
        (.inr (.inr (.inr (.inr (.inr (.inl Hty)))))) (fun _ => ⟨Hteq, Hterm⟩) (.inl Hrole) Hcfg
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun _ Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      $$ [$Hphys] as %err %s1 %dropped ⟨Hphys, %Hres, Herrn⟩
    · isplitl []
      · iintro %Hc; exfalso; rw [Hty] at Hc
        first | (rcases Hc with Hc | Hc <;> exact absurd Hc (by w32_ne)) | exact absurd Hc (by w32_ne)
      isplitl []
      · iintro %_
        isplitr
        · ipureintro
          exact ⟨Hscope, Hfid⟩
        · iframe Hsv Hvs
      · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
    obtain ⟨rfl, pvs, Hhs⟩ := candidateStepResult_snap _ _ _ _ _ _ _ _ Hty Hres
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    iapply HΦ $$ %interface.nil %s1
    iframe Hphys
    ipureintro
    refine ⟨nstateWf_handle_snap _ _ _ _ _ ?_ Hhs, ⟨[absSnap m sv voters], ?_, ?_⟩, rfl⟩
    · exact ⟨rfl, rfl⟩
    · intro m' Hm'
      exact List.mem_singleton.mp Hm'
    · exact step_handle_snap cfg id _ _ m sv voters s1 (adopt_candidate s m.From' pvs (by rw [Hrole]; decide)) Hto Hteq
        (by simp [toPState, Hrole, proleRole]) Hfid Hscope Hcfg Hhs
  · -- Leader: excluded
    exact absurd Hrole Hnl
  · -- PreCandidate (2026-10-04), as a candidate: `becomeFollower(r.Term, m.From)`, then
    -- `handleSnapshot`
    simp only [stepFuncOf]
    wp_apply _P.stepCandidate cfg r id s m [] sv voters []
        (.inr (.inr (.inr (.inr (.inr (.inl Hty)))))) (fun _ => ⟨Hteq, Hterm⟩) (.inr Hrole) Hcfg
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun _ Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      $$ [$Hphys] as %err %s1 %dropped ⟨Hphys, %Hres, Herrn⟩
    · isplitl []
      · iintro %Hc; exfalso; rw [Hty] at Hc
        first | (rcases Hc with Hc | Hc <;> exact absurd Hc (by w32_ne)) | exact absurd Hc (by w32_ne)
      isplitl []
      · iintro %_
        isplitr
        · ipureintro
          exact ⟨Hscope, Hfid⟩
        · iframe Hsv Hvs
      · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
    obtain ⟨rfl, pvs, Hhs⟩ := candidateStepResult_snap _ _ _ _ _ _ _ _ Hty Hres
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    iapply HΦ $$ %interface.nil %s1
    iframe Hphys
    ipureintro
    refine ⟨nstateWf_handle_snap _ _ _ _ _ ?_ Hhs, ⟨[absSnap m sv voters], ?_, ?_⟩, rfl⟩
    · exact ⟨rfl, rfl⟩
    · intro m' Hm'
      exact List.mem_singleton.mp Hm'
    · exact step_handle_snap cfg id _ _ m sv voters s1 (adopt_candidate s m.From' pvs (by rw [Hrole]; decide)) Hto Hteq
        (by simp [toPState, Hrole, proleRole]) Hfid Hscope Hcfg Hhs

end StepProof

end branches

end EtcdGrove
end Perennial
