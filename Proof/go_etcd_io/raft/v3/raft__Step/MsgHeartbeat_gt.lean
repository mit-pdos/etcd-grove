/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgHeartbeat_gt.v.

One term case of `Step`'s `MsgHeartbeat` branch (the incoming term is higher:
`becomeFollower(m.Term, m.From)`, then `stepFollower`), in its own file so that it
checks in parallel with the others; `proof_raft__Step_MsgHeartbeat.v` combines them.
Proof structure, not specification: no `Module Type`, no `Parameter`; only files in this
directory may `Require` it.

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

theorem wp_Step_MsgHeartbeat_gt (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) (ctx : List w8) :
    m.Type' = MsgHeartbeat →
    m.To' = id →
    m.Term' ≠ W64 0 →
    m.From' ≠ W64 0 →
    m.From' ≠ id →
    id ∈ cfg →
    NStateWf s →
    -- protocol fact (`heartbeat_commit_le_last`)
    uint.Z m.Commit' ≤ plogLastIndexZ s.logst.prev (s.logst.sents ++ s.logst.uents) →
    -- this file: the incoming term is higher: `becomeFollower(m.Term, m.From)`, then
    -- `stepFollower`
    uint.Z s.term < uint.Z m.Term' →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhys cfg r id s ∗
        "#Hents" ∷ m.Entries' ↦*□ ents ∗
        "#Hctx" ∷ m.Context' ↦*□ ctx }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhys cfg r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absMsg .heartbeat m ents ctx) ∧
            Step cfg id (toPState s) recv (toPState s')⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ }} := by
  intro Hty Hto Hterm Hfnz Hfid Hcfg Hwf Hcommit Hgt
  wp_start as ⟨Hphys, #Hents, #Hctx⟩
  wp_auto
  wp_apply _P.traceReceiveMessage
  rw [decide_eq_false Hterm]
  wp_auto
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  rw [decide_eq_true Hgt]
  wp_auto
  repeat (rw [Hty]; wp_auto)
  -- "received a message with higher term"
  wp_apply raft.wp_load_id $$ Hphys as Hphys
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  wp_raft_log
  -- MsgApp || MsgHeartbeat || MsgSnap: the second holds
  repeat (rw [Hty]; wp_auto)
  -- becomeFollower(m.Term, m.From): a leader's message
  wp_apply _P.becomeFollower cfg r id s m.Term' m.From' (Int.le_of_lt Hgt) $$ [$Hphys] as %pvs Hphys
  repeat (rw [Hty]; wp_auto)
  wp_apply raft.wp_load_step $$ Hphys as Hphys
  rw [show ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState).stepfn
      = functions stepFollower [] from rfl]
  wp_apply _P.stepFollower cfg r id
      ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState) m ents (zero_val _) [] ctx (.inr (.inr (.inr (.inl Hty))))
      (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      (fun _ => ⟨Hcommit, Hfid⟩)
      (fun Hc => by exfalso; rcases Hc with Hc | Hc <;> rw [Hty] at Hc <;> exact absurd Hc (by w32_ne))
    $$ [$Hphys] as %err %s1 %dropped ⟨Hphys, %Hres, Herrn⟩
  · isplitl []
    · iintro _; iexact Hctx
    isplitl []
    · iintro %Hc; exfalso; rw [Hty] at Hc
      rcases Hc with Hc | Hc <;> exact absurd Hc (by w32_ne)
    isplitl []
    · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
    · iintro %Hc; exfalso; rw [Hty] at Hc
      rcases Hc with Hc | Hc <;> exact absurd Hc (by w32_ne)
  obtain ⟨rfl, rfl⟩ := followerStepResult_heartbeat _ _ _ _ _ _ _ _ Hty Hres
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Herrn with %Herrn
  subst Herrn
  wp_auto
  iapply HΦ $$ %interface.nil %_
  iframe Hphys
  ipureintro
  refine ⟨nstateWf_heartbeatResult _ _ _ _ ?_, ?_, rfl,
    stepdown_frame (by rw [Hty]; w32_ne) (Int.le_of_lt Hgt) rfl rfl rfl rfl rfl⟩
  · exact ⟨rfl, rfl⟩
  · refine ⟨[absMsg .heartbeat m ents ctx] ++ [absMsg .heartbeat m ents ctx], ?_, ?_⟩
    · intro m' Hm'
      simp only [List.mem_append, List.mem_singleton, or_self] at Hm'
      exact Hm'
    · refine .trans _ _ _ _ _
        (step_higher_term_leader cfg id (toPState s) .heartbeat m ents ctx rfl Hgt Hto Hfid) ?_
      exact step_handle_heartbeat cfg id _ _ m ents ctx
        (adopt_after_stepdown s m.Term' m.From' pvs) Hto rfl (by simp [pbecomeFollower]) Hcommit Hfid

end StepProof

end branches

end EtcdGrove
end Perennial
