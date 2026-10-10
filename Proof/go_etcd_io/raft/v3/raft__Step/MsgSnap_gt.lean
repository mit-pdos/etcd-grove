/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgSnap_gt.v.

One term case of `Step`'s `MsgSnap` branch (the incoming term is higher:
`becomeFollower(m.Term, m.From)`, then `stepFollower`'s `MsgSnap` arm), in its own file
so that it checks in parallel with the others; `MsgSnap.lean` combines them. Proof
structure, not specification: no `Module Type`, no `Parameter`; only files in this
directory may import it.

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
variable [AllG GF]

namespace StepProof

theorem wp_Step_MsgSnap_gt (_P : raft.Step.Postulates (GF := GF) (hG := hG))
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
    -- this file: the incoming term is higher
    uint.Z s.term < uint.Z m.Term' →
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
  intro Hty Hto Hterm Hfnz Hfid Hcfg Hwf Hscope Hgt
  wp_start as ⟨Hphys, #Hsv, #Hvs⟩
  wp_auto
  wp_apply _P.traceReceiveMessage
  rw [decide_eq_false Hterm]
  wp_auto
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  rw [decide_eq_true Hgt]
  wp_auto
  -- (Type == MsgVote) || (Type == MsgPreVote): both false; the switch on MsgPreVote /
  -- MsgPreVoteResp: neither
  repeat (rw [Hty]; wp_auto)
  -- "received a message with higher term"
  wp_apply raft.wp_load_id $$ Hphys as Hphys
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  wp_raft_log
  -- MsgApp || MsgHeartbeat || MsgSnap: the third holds
  repeat (rw [Hty]; wp_auto)
  -- becomeFollower(m.Term, m.From): a leader's message
  wp_apply _P.becomeFollower cfg r id s m.Term' m.From' (Int.le_of_lt Hgt) $$ [$Hphys] as %pvs Hphys
  repeat (rw [Hty]; wp_auto)
  wp_apply raft.wp_load_step $$ Hphys as Hphys
  rw [show ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState).stepfn
      = functions stepFollower [] from rfl]
  wp_apply _P.stepFollower cfg r id
      ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState) m [] sv voters
      (.inr (.inr (.inr (.inr (.inr (.inl Hty))))))
      (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
    $$ [$Hphys] as %err %s1 %dropped ⟨Hphys, %Hres, Herrn⟩
  · isplitl []
    · iintro %_
      isplitr
      · ipureintro
        exact ⟨Hscope, rfl, rfl, Hcfg, Hfid⟩
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
  refine ⟨nstateWf_handle_snap _ _ _ _ _ ?_ Hhs, ?_, rfl⟩
  · exact ⟨rfl, rfl⟩
  refine ⟨[absSnap m sv voters] ++ [absSnap m sv voters], ?_, ?_⟩
  · intro m' Hm'
    simp only [List.mem_append, List.mem_singleton, or_self] at Hm'
    exact Hm'
  · refine .trans _ _ _ _ _ (step_higher_term_snap cfg id (toPState s) m sv voters Hgt Hto Hfid) ?_
    exact step_handle_snap cfg id _ _ m sv voters s1
      (adopt_after_stepdown s m.Term' m.From' pvs) Hto rfl (by simp [pbecomeFollower]) Hfid
      Hscope Hcfg Hhs

end StepProof

end branches

end EtcdGrove
end Perennial
