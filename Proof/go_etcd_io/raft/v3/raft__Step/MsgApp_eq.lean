/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgApp_eq.v.

One term case of `Step`'s `MsgApp` branch (the current term: `r.step(m)`, by role), in
its own file so that it checks in parallel with the others; `proof_raft__Step_MsgApp.v`
combines them. Proof structure, not specification: no `Module Type`, no `Parameter`;
only files in this directory may `Require` it.

Lean notes:
* The branch lemma takes the callee specs (Rocq's functor argument
  `P : STEP_POSTULATES`) as its first argument `_P : raft.Step.Postulates`, and Rocq's
  section variable `cfg` as its second.
* Rocq's `Local Ltac`s `recv_elem` (closing `∀ m' ∈ recv, m' = …` goals: `elem_of_app`,
  `list_elem_of_singleton`, `elem_of_nil`, `naive_solver`) and `wp_load_step` (the load
  of `r.step` in `r.step(r, m)`, bound by hand with `raft.wp_load_step`, as `wp_apply`
  does not find a load in function position) are not ported.
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

theorem wp_Step_MsgApp_eq (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) :
    m.Type' = MsgApp →
    m.To' = id →
    m.Term' ≠ W64 0 →
    m.From' ≠ W64 0 →
    m.From' ≠ id →
    id ∈ cfg →
    NStateWf s →
    -- protocol facts the dispatch derives from the ghost state (`app_recv_wf`,
    -- `app_no_conflict_below_commit`)
    PlogWf (entryID.mk m.LogTerm' m.Index') ents →
    uint.Z m.Index' + (ents.length : Int) + 1 < 2^64 →
    (∀ e ∈ ents, e.Type' = EntryNormal) →
    (uint.Z s.logst.committed ≤ uint.Z m.Index' →
     PlogMatches s.logst.prev (s.logst.sents ++ s.logst.uents)
       (entryID.mk m.LogTerm' m.Index') →
     plogFindConflict s.logst.prev (s.logst.sents ++ s.logst.uents) ents = W64 0 ∨
     uint.Z s.logst.committed <
       uint.Z (plogFindConflict s.logst.prev (s.logst.sents ++ s.logst.uents) ents)) →
    -- this file: the current term: `r.step(m)`, by role
    m.Term' = s.term →
    -- a follower's vote tally is empty (`padoptLeader` clears it, and `NStateWf` does
    -- not say so); see the combining file
    (s.role = .follower → s.votes = ∅) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhys cfg r id s ∗
        "#Hents" ∷ m.Entries' ↦*□ ents ∗
        "Hcap" ∷ ownSliceCap raftpb.Entry m.Entries' (DFrac.own 1) }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhys cfg r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absMsg .app m ents) ∧
            Step cfg id (toPState s) recv (toPState s')⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ }} := by
  intro Hty Hto Hterm Hfnz Hfid Hcfg Hwf Hpwf Hnw Hnorm Hconf Hteq Hvotes
  wp_start as Hphys
  iNamed Hphys
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
  repeat (rw [Hty]; wp_auto)
  wp_apply raft.wp_load_step $$ Hphys as Hphys
  rw [show s.stepfn = stepFuncOf s.role from Hwf.1]
  cases Hrole : s.role
  · -- Follower: `stepFollower`'s arm, with `r.lead = m.From`
    simp only [stepFuncOf]
    have Hvs := Hvotes Hrole
    wp_apply _P.stepFollower cfg r id s m ents (zero_val _) [] [] (.inr (.inr (.inl Hty)))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun _ => ⟨Hpwf, Hnw, Hnorm, Hconf, Hfid⟩)
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      $$ [$Hphys Hcap] as %err %s1 %dropped ⟨Hphys, %Hres, Herrn⟩
    · isplitl []
      · iintro %Hc; exfalso; rw [Hty] at Hc
        first | (rcases Hc with Hc | Hc <;> exact absurd Hc (by w32_ne)) | exact absurd Hc (by w32_ne)
      isplitl []
      · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
      · iintro %_; iframe Hents Hcap
    obtain ⟨rfl, Happ⟩ := followerStepResult_app _ _ _ _ _ _ _ Hty Hres
    have Hwf1 : NStateWf { s with lead := m.From' } := Hwf
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    iapply HΦ $$ %interface.nil %s1
    iframe Hphys
    ipureintro
    refine ⟨nstateWf_handle_app _ _ _ _ _ Hwf1 Happ, ⟨[absMsg .app m ents], ?_, ?_⟩, rfl,
      app_frame Hty Happ (NetFrame.refl _) (Int.le_refl _) (Int.le_max_left _ _)⟩
    · intro m' Hm'; simpa using Hm'
    · exact step_handle_app cfg id _ _ m ents s1 (adopt_follower s m.From' Hrole Hvs) Hto Hteq
        (by simp [toPState, Hrole, proleRole]) Hconf Happ Hfid
  · -- Candidate: `becomeFollower(r.Term, m.From)`, then the handler
    simp only [stepFuncOf]
    wp_apply _P.stepCandidate cfg r id s m ents (zero_val _) [] [] (.inr (.inr (.inl Hty)))
        (fun _ => ⟨Hteq, Hterm⟩) (.inl Hrole) Hcfg (fun _ => ⟨Hpwf, Hnw, Hnorm, Hconf, Hfid⟩)
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun _ Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      $$ [$Hphys Hcap] as %err %s1 %dropped ⟨Hphys, %Hres, Herrn⟩
    · isplitl []
      · iintro %Hc; exfalso; rw [Hty] at Hc
        first | (rcases Hc with Hc | Hc <;> exact absurd Hc (by w32_ne)) | exact absurd Hc (by w32_ne)
      isplitl []
      · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
      · iintro %_; iframe Hents Hcap
    obtain ⟨rfl, pvs, Happ⟩ := candidateStepResult_app _ _ _ _ _ _ _ _ Hty Hres
    have Hwf1 : NStateWf
        ({ becomeFollower s s.term m.From' with prvals := pvs } : NState) := ⟨rfl, rfl⟩
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    iapply HΦ $$ %interface.nil %s1
    iframe Hphys
    ipureintro
    refine ⟨nstateWf_handle_app _ _ _ _ _ Hwf1 Happ, ⟨[absMsg .app m ents], ?_, ?_⟩, rfl,
      app_frame Hty Happ (NetFrame.refl _) (Int.le_refl _) (Int.le_max_left _ _)⟩
    · intro m' Hm'; simpa using Hm'
    · exact step_handle_app cfg id _ _ m ents s1 (adopt_candidate s m.From' pvs) Hto Hteq
        (by simp [toPState, Hrole, proleRole]) Hconf Happ Hfid
  · -- Leader: `stepLeader` has no arm for it; nothing changes
    simp only [stepFuncOf]
    wp_apply _P.stepLeader cfg r id s m [] (.inr (.inr (.inr (.inr (.inr (.inl Hty))))))
        Hrole Hcfg
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by
          exfalso; rw [Hty] at Hc
          rcases Hc with Hc | ⟨Hc, -⟩ <;> exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      $$ [$Hphys] as %err %s' %dropped ⟨Hphys, %Hres, Herrn, -⟩
    · isplitl []
      · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
      · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
    obtain ⟨rfl, rfl⟩ := leaderStepResult_app_hb _ _ _ _ _ _ _ (.inl Hty) Hres
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    iapply HΦ $$ %interface.nil %_
    iframe Hphys
    ipureintro
    exact ⟨Hwf, ⟨[], fun _ h => absurd h List.not_mem_nil, .refl _⟩, rfl,
      keep_frame rfl rfl rfl rfl rfl⟩
  · -- PreCandidate (2026-10-04), as a candidate: `becomeFollower(r.Term, m.From)`, then
    -- the handler
    simp only [stepFuncOf]
    wp_apply _P.stepCandidate cfg r id s m ents (zero_val _) [] [] (.inr (.inr (.inl Hty)))
        (fun _ => ⟨Hteq, Hterm⟩) (.inr Hrole) Hcfg (fun _ => ⟨Hpwf, Hnw, Hnorm, Hconf, Hfid⟩)
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun _ Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      $$ [$Hphys Hcap] as %err %s1 %dropped ⟨Hphys, %Hres, Herrn⟩
    · isplitl []
      · iintro %Hc; exfalso; rw [Hty] at Hc
        first | (rcases Hc with Hc | Hc <;> exact absurd Hc (by w32_ne)) | exact absurd Hc (by w32_ne)
      isplitl []
      · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
      · iintro %_; iframe Hents Hcap
    obtain ⟨rfl, pvs, Happ⟩ := candidateStepResult_app _ _ _ _ _ _ _ _ Hty Hres
    have Hwf1 : NStateWf
        ({ becomeFollower s s.term m.From' with prvals := pvs } : NState) := ⟨rfl, rfl⟩
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    iapply HΦ $$ %interface.nil %s1
    iframe Hphys
    ipureintro
    refine ⟨nstateWf_handle_app _ _ _ _ _ Hwf1 Happ, ⟨[absMsg .app m ents], ?_, ?_⟩, rfl,
      app_frame Hty Happ (NetFrame.refl _) (Int.le_refl _) (Int.le_max_left _ _)⟩
    · intro m' Hm'; simpa using Hm'
    · exact step_handle_app cfg id _ _ m ents s1 (adopt_candidate s m.From' pvs) Hto Hteq
        (by simp [toPState, Hrole, proleRole]) Hconf Happ Hfid

end StepProof

end branches

end EtcdGrove
end Perennial
