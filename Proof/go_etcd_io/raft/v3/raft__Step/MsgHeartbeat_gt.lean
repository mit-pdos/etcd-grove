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
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
    (ents : List EntryM) (R : StepG GF) :
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
        "Hm" ∷ msgIn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ ∗
        -- (2026-11-10, Q8 stage 1 slice 11) the caller's resource and `Step`'s gates
        "HG" ∷ R.G ∗ "Hgates" ∷ stepGates c r id s m ents sn ctx rs R }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s' ∗
        -- (Q8 stage 1 slice 13) the end state on the path (`StepEnd`, `LemmasStepGates.lean`)
        "%Hend" ∷ ⌜StepEnd c id m ents ctx s s'⌝ ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absMsg .heartbeat m ents ctx) ∧
            StepCD c id B m s recv s'⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ ∗
        "HG" ∷ stepOut R s'.outbox }} := by
  intro Hty Hto Hterm Hfnz Hfid Hwf Hcommit Hgt
  wp_start as H
  iNamed H
  icases msgPtsC_nn _ _ _ _ _ $$ Hm with ⟨%Hnn, Hm⟩
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_recv_gate_ns
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
  have hbf : PreBF m s := PreBF.of_gt Hgt (by rw [Hty]; w32_ne) (fun h => absurd (Hty.symm.trans h) (by w32_ne))
  have hlead : preLead m = m.From' := preLead_from (.inr (.inl Hty))
  ihave Hgb := preGate_bf c r id s m R.G0 R.G1 m.From' hbf hlead $$ Hgpre HG
  wp_apply _P.becomeFollower c r id s m.Term' m.From' (R.G1 s.outbox) (Int.le_of_lt Hgt) (fun _ => rfl) $$ [$Hphys $Hgb]
    as %pvs ⟨Hphys, HG⟩
  phys_idx HG
  wp_drive _Q
  wp_apply raft.wp_load_stepC $$ Hphys as Hphys
  rw [show ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState).stepfn
      = functions stepFollower [] from rfl]
  ihave #Hsrc0 : rcvSrc (GF := GF) ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState).gh.sn m.Type' sn $$ []
  · iapply rcvSrc_ne; notsnap_tac
  ihave Hfg := stepFnGates_follower c r id s m ents ctx R pvs _ (preState_bf' hbf hlead pvs) rfl $$ Hgstep
  wp_apply _P.stepFollower c ∅ r id
      ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState) ml m ents sn rs (zero_val _) ctx
      R.G1 R.GE (.inr (.inr (.inr (.inl Hty))))
      (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne)) (by intro _; simp only [becomeFollower, resetTo, resetTo0]; exact Hterm)
      (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      (fun _ => ⟨Hcommit, Hfid⟩)
      (fun Hc => by exfalso; rcases Hc with Hc | Hc <;> rw [Hty] at Hc <;> exact absurd Hc (by w32_ne))
      (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
    (by notfwd_tac) Hgok.1 Hgok.2.1 $$ [$Hphys Hm $Hsrc0 $HG Hfg] as %err %s1 %dropped %c1 ⟨Hphys, %Hres, Herrn, HGo⟩
  · isplitl [Hm]
    · iapply msgIn_nonprop (by rw [Hty]; w32_ne) $$ Hm
    · iunfold followerGates at Hfg; iexact Hfg
  ihave HG := stepOut_or R _ _ $$ HGo
  obtain ⟨rfl, rfl, rfl⟩ := followerStepResult_heartbeat _ _ _ _ _ _ _ _ _ Hty Hres
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Herrn with %Herrn
  subst Herrn
  wp_auto
  try phys_out
  iapply HΦ $$ %interface.nil %_
  iframe Hphys HG
  ipureintro
  refine ⟨StepEnd.fn_bf hbf hlead (by rw [Hty]; w32_ne) (by rw [Hty]; w32_ne) pvs
      (StepFnEnd.follower rfl Hres), nstateWf_heartbeatResult _ _ _ _ ?_, ?_, rfl,
    stepdown_frame (by rw [Hty]; w32_ne) (Int.le_of_lt Hgt) rfl rfl rfl rfl rfl⟩
  · exact ⟨rfl, rfl⟩
  · refine ⟨[absMsg .heartbeat m ents ctx] ++ [absMsg .heartbeat m ents ctx], ?_, ?_⟩
    · intro m' Hm'
      simp only [List.mem_append, List.mem_singleton, or_self] at Hm'
      exact Hm'
    · refine StepCD.frame ?_ (by rframe)
      refine .trans _ _ _ _ _
        (step_higher_term_leader c id (toPState s) .heartbeat m ents ctx rfl Hgt Hto Hfid) ?_
      exact step_handle_heartbeat c id _ _ m ents ctx
        (adopt_after_stepdown s m.Term' m.From' pvs) Hto rfl (by simp [pbecomeFollower]) Hcommit Hfid

end StepProof

end branches

end EtcdGrove
end Perennial
