/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgHeartbeat_gt.v.

One term case of `Step`'s `MsgHeartbeat` branch (the incoming term is higher:
`becomeFollower(m.Term, m.From)`, then `stepFollower`), in its own file so that it
checks in parallel with the others; `proof_raft__Step_MsgHeartbeat.v` combines them.
Proof structure, not specification: no `Module Type`, no `Parameter`; only files in this
directory may `Require` it.

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
theorem wp_Step_MsgHeartbeat_gt (_P : raft.Step.Postulates (GF := GF) (hG := hG))
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
    -- this file: the incoming term is higher: `becomeFollower(m.Term, m.From)`, then
    -- `stepFollower`
    uint.Z s.term < uint.Z m.Term' →
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
  intro Hty Hto Hterm Hfnz Hfid Hwf Hcommit Hgt
  wp_start as H
  iNamed H
  icases msgPtsC_not_null _ _ _ _ _ $$ Hm with ⟨%Hnn, Hm⟩
  icases ownRaftPhysC_prvals_ok c r id s $$ Hphys with ⟨-, %HnwL, Hphys⟩
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply _P.traceReceiveMessage
  try wp_auto
  wp_get _Q
  rw [decide_eq_false Hterm]
  wp_auto
  wp_drive _Q
  rw [decide_eq_true Hgt]
  wp_auto
  wp_drive _Q
  -- "received a message with higher term"
  wp_drive _Q
  wp_raft_logC
  -- MsgApp || MsgHeartbeat || MsgSnap: the second holds
  wp_drive _Q
  -- becomeFollower(m.Term, m.From): a leader's message
  wp_apply _P.becomeFollower c r id s m.Term' m.From' (Int.le_of_lt Hgt) $$ [$Hphys] as %pvs Hphys
  wp_drive _Q
  wp_apply raft.wp_load_stepC $$ Hphys as Hphys
  rw [show ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState).stepfn
      = functions stepFollower [] from rfl]
  wp_apply _P.stepFollower c ∅ r id
      ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState) ml m ents sn rs (zero_val _) ctx (.inr (.inr (.inr (.inl Hty))))
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
  refine ⟨nstateWf_heartbeatResult _ _ _ _ ?_, ?_, rfl,
    stepdown_frame (by rw [Hty]; w32_ne) (Int.le_of_lt Hgt) rfl rfl rfl rfl rfl⟩
  · exact nstateWf_becomeFollower s m.Term' m.From' Hwf.2.2 (Int.le_of_lt Hgt)
  · refine ⟨[absMsg .heartbeat m ents ctx] ++ [absMsg .heartbeat m ents ctx], ?_, ?_⟩
    · intro m' Hm'
      simp only [List.mem_append, List.mem_singleton, or_self] at Hm'
      exact Hm'
    · refine StepCD.frame ?_ (by rframe)
      refine .trans _ _ _ _ _
        (step_higher_term_leader c id (toPState s) .heartbeat m ents ctx rfl Hgt Hto Hfid) ?_
      exact step_handle_heartbeat c id _ _ m ents ctx
        (adopt_after_stepdown s m.Term' m.From' pvs) Hto rfl (by simp [pbecomeFollower]) Hcommit Hfid HnwL

end StepProof

end branches

end EtcdGrove
end Perennial
