/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgSnap_gt.v.

One term case of `Step`'s `MsgSnap` branch (the incoming term is higher:
`becomeFollower(m.Term, m.From)`, then `stepFollower`'s `MsgSnap` arm), in its own file
so that it checks in parallel with the others; `MsgSnap.lean` combines them. Proof
structure, not specification: no `Module Type`, no `Parameter`; only files in this
directory may import it.

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

theorem wp_Step_MsgSnap_gt (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (scfg : CSLists) (sv : raftpb.Snapshot) :
    m.Type' = MsgSnap →
    m.To' = id →
    m.Term' ≠ W64 0 →
    m.From' ≠ W64 0 →
    m.From' ≠ id →
    scfg.Has id →
    NStateWf s →
    SnapScope sv scfg →
    -- this file: the incoming term is higher
    uint.Z s.term < uint.Z m.Term' →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
        "#Hsv" ∷ m.Snapshot' ↦□ sv ∗
        "#Hcs" ∷ ownCSL sv.Metadata'.ConfState' scfg }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
    {{ (err : GoInterface) (s' : NState) (c' : CfgM), RET #err;
        "Hphys" ∷ ownRaftPhysCV c' c'.voters r id s' ∗
        -- (2026-10-14, stage B7) the snapshot's configuration after a restore
        "%Hc'" ∷ ⌜c' = c ∨ c' = snapCfg sv scfg⌝ ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absSnap m sv scfg) ∧
            StepCDS c c' (snapCfg sv scfg) id (snapId sv) s recv s'⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ }} := by
  intro Hty Hto Hterm Hfnz Hfid Hcfg Hwf Hscope Hgt
  wp_start as ⟨Hphys, #Hsv, #Hcs⟩
  wp_auto
  wp_apply _P.traceReceiveMessage
  rw [decide_eq_false Hterm]
  wp_auto
  wp_apply raft.wp_load_TermC $$ Hphys as Hphys
  rw [decide_eq_true Hgt]
  wp_auto
  -- (Type == MsgVote) || (Type == MsgPreVote): both false; the switch on MsgPreVote /
  -- MsgPreVoteResp: neither
  repeat (rw [Hty]; wp_auto)
  -- "received a message with higher term"
  wp_apply raft.wp_load_idC $$ Hphys as Hphys
  wp_apply raft.wp_load_TermC $$ Hphys as Hphys
  wp_raft_logC
  -- MsgApp || MsgHeartbeat || MsgSnap: the third holds
  repeat (rw [Hty]; wp_auto)
  -- becomeFollower(m.Term, m.From): a leader's message
  wp_apply _P.becomeFollower c r id s m.Term' m.From' (Int.le_of_lt Hgt) $$ [$Hphys] as %pvs Hphys
  repeat (rw [Hty]; wp_auto)
  wp_apply raft.wp_load_stepC $$ Hphys as Hphys
  rw [show ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState).stepfn
      = functions stepFollower [] from rfl]
  wp_apply _P.stepFollower c scfg r id
      ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState) m [] sv []
      (.inr (.inr (.inr (.inr (.inr (.inl Hty))))))
      (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      (fun Hc => by exfalso; rcases Hc with Hc | Hc <;> rw [Hty] at Hc <;> exact absurd Hc (by w32_ne))
    $$ [$Hphys] as %err %s1 %dropped %c1 ⟨Hphys, %Hres, Herrn⟩
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
        exact ⟨Hscope, rfl, rfl, Hcfg, Hfid⟩
      · iframe Hsv Hcs
    · iintro %Hc; exfalso; rw [Hty] at Hc
      rcases Hc with Hc | Hc <;> exact absurd Hc (by w32_ne)
  obtain ⟨Hc1, rfl, Hhs⟩ := followerStepResult_snap _ _ _ _ _ _ _ _ Hty Hres
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Herrn with %Herrn
  subst Herrn
  wp_auto
  iapply HΦ $$ %interface.nil %s1 %c1
  iframe Hphys
  ipureintro
  refine ⟨snapCfgOk_cases Hc1, nstateWf_handle_snap _ _ _ _ _ ?_ Hhs, ?_, rfl⟩
  · exact ⟨rfl, rfl⟩
  refine ⟨[absSnap m sv scfg] ++ [absSnap m sv scfg], ?_, ?_⟩
  · intro m' Hm'
    simp only [List.mem_append, List.mem_singleton, or_self] at Hm'
    exact Hm'
  · -- the step-down (a frame step), then `handleSnapshot` on the follower
    have e : toPState ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState) =
        pbecomeFollower (toPState s) m.Term' m.From' := by
      rw [toPState_prvals_nl _ _ (by simp [becomeFollower]), toPState_becomeFollower]
    have Hcf := stepCF_higher_term_snap c id (toPState s) m sv scfg Hgt Hto Hfid
    rw [← e] at Hcf
    refine StepCDS.trans_frame Hcf ⟨by simp [becomeFollower, resetTo, resetTo0],
      by simp [becomeFollower, resetTo, resetTo0], fun h => by simp [becomeFollower] at h⟩ ?_
    exact stepCDS_handle_snap c _ c1 id _ _ m sv scfg s1
      (adopt_follower _ m.From' rfl rfl) rfl (by simp [becomeFollower]) rfl Hto
      (by simp [toPState, becomeFollower, resetTo, resetTo0]) Hfid Hhs Hc1

end StepProof

end branches

end EtcdGrove
end Perennial
