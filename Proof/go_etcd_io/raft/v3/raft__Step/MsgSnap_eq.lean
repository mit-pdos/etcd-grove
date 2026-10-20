/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgSnap_eq.v.

One term case of `Step`'s `MsgSnap` branch (the current term: `r.step(m)` by role), in
its own file so that it checks in parallel with the others; `MsgSnap.lean` combines
them. A leader is excluded by a premise (the dispatch refutes a second leader of the
term, `isLeader_unique`). Proof structure, not specification: no `Module Type`, no
`Parameter`; only files in this directory may import it.

Lean notes:
* The branch lemmas take the callee specs (Rocq's functor argument `P : STEP_POSTULATES`)
  as their first argument `_P : raft.Step.Postulates`, and Rocq's section variable `c`
  as their second.
* Rocq's `Local Ltac recv_elem` (closes `∀ m' ∈ recv, m' = a` for `recv` built from
  `[]` and `[a]`) is not ported.
* Rocq's `Local Ltac wp_load_step` (binds the load of `r.step` in function position and
  applies `raft.wp_load_stepC` to `"Hphys"`) is not ported.
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
theorem wp_Step_MsgSnap_eq (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (_Q : raft.Step.ReplPbPostulates (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc)
    (ents : List EntryM) (scfg : CSLists) (sv : SnapshotM)
    -- (2026-10-19, D21 M3) not in the no-snapshot mode (`raft.restore`'s premise)
    (Hnsf : s.gh.ns = false) :
    m.Type' = MsgSnap →
    m.To' = id →
    m.Term' ≠ W64 0 →
    m.From' ≠ W64 0 →
    m.From' ≠ id →
    NStateWf s →
    SnapScopeIf id sv scfg →
    -- (stage R4) the snapshot the message holds, and its `ConfState`'s lists
    sn = some sv →
    scfg = sv.Metadata'.ConfState'.lists →
    -- this file: the current term
    m.Term' = s.term →
    -- not a leader: the sender leads this term (`isLeader_unique`)
    s.role ≠ .leader →
    -- a follower's vote tally is empty (`FollowerVotesOk`)
    (s.role = .follower → s.votes = ∅) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
        "Hm" ∷ msgIn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ ∗
        -- (D22 S-b′3, 2026-10-20) the snapshot certified in the storage's registry
        "#Hcert" ∷ storCert s.logst.storage (snapTrip sv sv.Metadata'.ConfState'.lists) }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface) (s' : NState) (c' : CfgM), RET #err;
        "Hphys" ∷ ownRaftPhysCV c' c'.voters r id s' ∗
        -- (2026-10-14, stage B7) the snapshot's configuration after a restore
        "%Hc'" ∷ ⌜c' = c ∨ (c' = snapCfg sv scfg ∧ scfg.Has id)⌝ ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absSnap m sv scfg) ∧
            StepCDS c c' (snapCfg sv scfg) id B (snapId sv) s recv s'⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        -- (2026-10-19, D21 M3) the no-snapshot mode kept
        "%Hng" ∷ ⌜s'.gh = s.gh⌝ ∗
        -- (2026-10-20, D22 S-c) what is kept of the state, and the term (the node's)
        "%Hsf" ∷ ⌜SnapStep m s s'⌝ }} := by
  intro Hty Hto Hterm Hfnz Hfid Hwf Hscope Hsn Hscl Hteq Hnl Hvotes
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
    ihave #Hsrc0 : tsSrc (GF := GF) s.logst.storage m.Type' sn $$ []
    · rw [Hsn]
      iapply tsSrc_snap; iexact Hcert
    wp_apply _P.stepFollower c scfg r id s ml m ents sn rs sv ctx
        (.inr (.inr (.inr (.inr (.inr (.inl Hty))))))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by exfalso; rcases Hc with Hc | Hc <;> rw [Hty] at Hc <;> exact absurd Hc (by w32_ne))
        (fun _ => ⟨Hsn, Hscl, Hscope, Hrole, Hvs, Hfid, Hnsf⟩)
      $$ [$Hphys Hm $Hsrc0] as %err %s1 %dropped %c1 ⟨Hphys, %Hres, Herrn⟩
    · iapply msgIn_nonprop (by rw [Hty]; w32_ne) $$ Hm
    obtain ⟨Hc1, rfl, Hhs⟩ := followerStepResult_snap _ _ _ _ _ _ _ _ Hty Hres
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    iapply HΦ $$ %interface.nil %s1 %c1
    iframe Hphys
    ipureintro
    refine ⟨snapCfgOk_cases' Hc1, nstateWf_handle_snap (t := { s with lead := m.From' }) _ _ _ _ Hwf Hhs,
      ⟨[absSnap m sv scfg], ?_, ?_⟩, rfl, by rw [HandleSnapResult.ns Hhs]; try simp [becomeFollower, resetTo, resetTo0],
      SnapStep.of_handle (t := { s with lead := m.From' }) rfl rfl rfl (Int.le_refl _)
        (Int.le_max_left _ _) Hrole Hhs⟩
    · intro m' Hm'
      exact List.mem_singleton.mp Hm'
    · exact stepCDS_handle_snap c c1 id s _ m sv scfg s1
        (adopt_follower s m.From' Hrole Hvs) rfl (by rw [Hrole]; decide) Hrole Hto Hteq Hfid Hhs
        Hc1
  · -- Candidate: `becomeFollower(r.Term, m.From)`, then `handleSnapshot`
    simp only [stepFuncOf]
    ihave #Hsrc0 : tsSrc (GF := GF) s.logst.storage m.Type' sn $$ []
    · rw [Hsn]
      iapply tsSrc_snap; iexact Hcert
    wp_apply _P.stepCandidate c scfg r id s ml m ents sn rs sv ctx
        (.inr (.inr (.inr (.inr (.inr (.inl Hty)))))) (fun _ => ⟨Hteq, Hterm⟩) (.inl Hrole)
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun _ Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun _ => ⟨Hsn, Hscl, Hscope, Hfid, Hnsf⟩)
      $$ [$Hphys Hm $Hsrc0] as %err %s1 %dropped %c1 ⟨Hphys, %Hres, Herrn⟩
    · iapply msgIn_nonprop (by rw [Hty]; w32_ne) $$ Hm
    obtain ⟨Hc1, rfl, pvs, Hhs⟩ := candidateStepResult_snap _ _ _ _ _ _ _ _ Hty Hres
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    iapply HΦ $$ %interface.nil %s1 %c1
    iframe Hphys
    ipureintro
    refine ⟨snapCfgOk_cases' Hc1, nstateWf_handle_snap _ _ _ _ _ ?_ Hhs,
      ⟨[absSnap m sv scfg], ?_, ?_⟩, rfl, by rw [HandleSnapResult.ns Hhs]; try simp [becomeFollower, resetTo, resetTo0],
      SnapStep.of_handle (t := { becomeFollower s s.term m.From' with prvals := pvs })
        (by simp [becomeFollower, resetTo, resetTo0]) rfl
        (by simp [becomeFollower, resetTo, resetTo0])
        (by simp [becomeFollower, resetTo, resetTo0])
        (by simp only [becomeFollower, resetTo, resetTo0]; omega) rfl Hhs⟩
    · exact ⟨rfl, rfl⟩
    · intro m' Hm'
      exact List.mem_singleton.mp Hm'
    · exact stepCDS_handle_snap c c1 id s _ m sv scfg s1
        (adopt_candidate s m.From' pvs (by rw [Hrole]; decide))
        (by simp [becomeFollower, resetTo, resetTo0]) (by rw [Hrole]; decide)
        (by simp [becomeFollower]) Hto Hteq Hfid Hhs Hc1
  · -- Leader: excluded
    exact absurd Hrole Hnl
  · -- PreCandidate (2026-10-04), as a candidate: `becomeFollower(r.Term, m.From)`, then
    -- `handleSnapshot`
    simp only [stepFuncOf]
    ihave #Hsrc0 : tsSrc (GF := GF) s.logst.storage m.Type' sn $$ []
    · rw [Hsn]
      iapply tsSrc_snap; iexact Hcert
    wp_apply _P.stepCandidate c scfg r id s ml m ents sn rs sv ctx
        (.inr (.inr (.inr (.inr (.inr (.inl Hty)))))) (fun _ => ⟨Hteq, Hterm⟩) (.inr Hrole)
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun _ Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun _ => ⟨Hsn, Hscl, Hscope, Hfid, Hnsf⟩)
      $$ [$Hphys Hm $Hsrc0] as %err %s1 %dropped %c1 ⟨Hphys, %Hres, Herrn⟩
    · iapply msgIn_nonprop (by rw [Hty]; w32_ne) $$ Hm
    obtain ⟨Hc1, rfl, pvs, Hhs⟩ := candidateStepResult_snap _ _ _ _ _ _ _ _ Hty Hres
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    iapply HΦ $$ %interface.nil %s1 %c1
    iframe Hphys
    ipureintro
    refine ⟨snapCfgOk_cases' Hc1, nstateWf_handle_snap _ _ _ _ _ ?_ Hhs,
      ⟨[absSnap m sv scfg], ?_, ?_⟩, rfl, by rw [HandleSnapResult.ns Hhs]; try simp [becomeFollower, resetTo, resetTo0],
      SnapStep.of_handle (t := { becomeFollower s s.term m.From' with prvals := pvs })
        (by simp [becomeFollower, resetTo, resetTo0]) rfl
        (by simp [becomeFollower, resetTo, resetTo0])
        (by simp [becomeFollower, resetTo, resetTo0])
        (by simp only [becomeFollower, resetTo, resetTo0]; omega) rfl Hhs⟩
    · exact ⟨rfl, rfl⟩
    · intro m' Hm'
      exact List.mem_singleton.mp Hm'
    · exact stepCDS_handle_snap c c1 id s _ m sv scfg s1
        (adopt_candidate s m.From' pvs (by rw [Hrole]; decide))
        (by simp [becomeFollower, resetTo, resetTo0]) (by rw [Hrole]; decide)
        (by simp [becomeFollower]) Hto Hteq Hfid Hhs Hc1

end StepProof

end branches

end EtcdGrove
end Perennial
