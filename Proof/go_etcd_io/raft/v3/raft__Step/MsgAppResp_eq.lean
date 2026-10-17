/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgAppResp_eq.v.

The current-term case of `Step`'s `MsgAppResp` branch, in its own file so that it
checks in parallel with the other term cases -- see `MsgAppResp.lean`, which combines
them. Proof structure, not specification: no `Module Type`, no `Parameter`; only files
in this directory may import it.

Lean notes:
* The branch lemma takes the callee specs (Rocq's functor argument
  `P : STEP_POSTULATES`) as its first argument `_P : raft.Step.Postulates`, and Rocq's
  section variable `c` as its second.
* Rocq's `Local Ltac`s `recv_elem`, `wp_load_step`, `ne_ty` are not ported
  (proof-side helpers; the proof porter may write Lean macros or inline them).
-/
module

public import Proof.go_etcd_io.raft.v3.raft__Step.resp_lemmas
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
/-- `MsgAppResp` at `m.Term = r.Term`: the preamble does nothing and the type switch's
default arm runs `r.step(m)`. `stepFollower` and `stepCandidate` have no arm for it
(`StepC.refl`); `stepLeader` is the replication path, whose `LeaderStepResult` becomes
`StepC.appResp`/`StepC.commit`/`StepC.sendApps` (`leader_appresp_step`). -/
theorem wp_Step_MsgAppResp_eq (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (_Q : raft.Step.ReplPbPostulates (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc)
    (ents : List EntryM)
    (Hlrd : s.role = .leader → RdOk c.voters s.rd ∧ s.term ≠ W64 0)
    -- (2026-10-16, stage R8a, D11) at a leader an accepted acknowledgement of its term is within
    -- its log: `Step` has it from the message's ghost witness (`ackIn`)
    (Hack : s.role = .leader → m.Term' = s.term → m.Reject' = false →
      uint.Z m.Index' ≤ uint.Z (logLast s.logst)) :
    m.Type' = MsgAppResp →
    m.To' = id →
    m.Term' ≠ W64 0 →
    m.Term' = s.term →
    m.From' ≠ W64 0 →
    (m.Reject' = true → m.From' ≠ id) →
    NStateWf s →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
        "Hm" ∷ msgIn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absMsg .appResp m ents) ∧
            StepCD c id m s recv s'⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ }} := by
  intro Hty Hto Hterm Hteq Hfnz Hrej Hwf
  have Hty3 : m.Type' = MsgBeat ∨ m.Type' = MsgAppResp ∨ m.Type' = MsgHeartbeatResp :=
    .inr (.inl Hty)
  wp_start as H
  iNamed H
  icases msgPtsC_not_null _ _ _ _ _ $$ Hm with ⟨%Hnn, Hm⟩
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply _P.traceReceiveMessage
  try wp_auto
  wp_get _Q
  rw [decide_eq_false Hterm]
  wp_auto
  wp_drive _Q
  rw [decide_eq_false (show ¬ (uint.Z s.term < uint.Z m.Term') by rw [Hteq]; omega)]
  wp_auto
  wp_drive _Q
  rw [decide_eq_false (show ¬ (uint.Z m.Term' < uint.Z s.term) by rw [Hteq]; omega)]
  wp_auto
  -- the type switch: none of its four cases, so `r.step(m)`
  wp_drive _Q
  wp_apply raft.wp_load_stepC $$ Hphys as Hphys
  rw [show s.stepfn = stepFuncOf s.role from Hwf.1]
  have Hsnap0 : ∀ (P : IProp GF), ⊢ (⌜m.Type' = MsgSnap⌝ -∗ P : IProp GF) := fun P => by
    iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
  cases Hrole : s.role
  · -- Follower: no `MsgAppResp` arm
    simp only [stepFuncOf]
    wp_apply _P.stepFollower c ∅ r id s ml m ents sn rs (zero_val _) ctx
        (.inr (.inr (.inr (.inr (.inl Hty3)))))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by exfalso; rcases Hc with Hc | Hc <;> rw [Hty] at Hc <;> exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      $$ [$Hphys Hm] as %err %s1 %dropped %c1 ⟨Hphys, %Hres, Herrn⟩
    · iapply msgIn_nonprop (by rw [Hty]; w32_ne) $$ Hm
    obtain ⟨rfl, rfl, Hs1⟩ := followerStepResult_noop _ _ _ _ _ _ _ _ Hty3 Hres
    rw [Hs1]
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    iapply HΦ $$ %interface.nil %s
    iframe Hphys
    ipureintro
    exact ⟨Hwf, ⟨[], fun _ Hin => absurd Hin List.not_mem_nil, StepCD.frame (.refl _) (RFrame.refl _)⟩, rfl,
      keep_frame rfl rfl rfl rfl rfl⟩
  · -- Candidate: no `MsgAppResp` arm either
    simp only [stepFuncOf]
    wp_apply _P.stepCandidate c ∅ r id s ml m ents sn rs (zero_val _) ctx
        (.inr (.inr (.inr (.inr (.inl Hty3)))))
        (fun _ => ⟨Hteq, Hterm⟩)
        (.inl Hrole) (Hwf.2.2.1)
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun _ Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      $$ [$Hphys Hm] as %err %s1 %dropped %c1 ⟨Hphys, %Hres, Herrn⟩
    · iapply msgIn_nonprop (by rw [Hty]; w32_ne) $$ Hm
    obtain ⟨rfl, rfl, Hs1⟩ := candidateStepResult_noop _ _ _ _ _ _ _ _ Hty3 Hres
    rw [Hs1]
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    iapply HΦ $$ %interface.nil %s
    iframe Hphys
    ipureintro
    exact ⟨Hwf, ⟨[], fun _ Hin => absurd Hin List.not_mem_nil, StepCD.frame (.refl _) (RFrame.refl _)⟩, rfl,
      keep_frame rfl rfl rfl rfl rfl⟩
  · -- Leader: the replication path
    simp only [stepFuncOf]
    wp_apply _P.stepLeader c r id s ml m ents sn ctx rs (.inr (.inr (.inr (.inl Hty)))) Hrole
        (fun _ => Hfnz)
        (fun Hc => by
          rcases Hc with Hc | ⟨-, Hc⟩
          · exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
          · exact Hrej Hc)
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun _ => Hlrd Hrole)
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun _ hr => Hack Hrole Hteq hr)
      $$ [$Hphys Hm] as %err %s' %dropped ⟨Hphys, %Hres, Herrn⟩
    · isplitl [Hm]
      · iapply msgIn_nonprop (by rw [Hty]; w32_ne) $$ Hm
      · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
    obtain ⟨rfl, Hwf', ⟨recv, Hrecv, Hstep⟩, Hft⟩ :=
      leader_appresp_step c id s m ents ents dropped s' Hrole Hty Hto Hteq Hwf Hres
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    iapply HΦ $$ %interface.nil %s'
    iframe Hphys
    ipureintro
    exact ⟨Hwf', ⟨recv, Hrecv, Hstep⟩, rfl, Hft⟩
  · -- PreCandidate (2026-10-04), as a candidate: no `MsgAppResp` arm either
    simp only [stepFuncOf]
    wp_apply _P.stepCandidate c ∅ r id s ml m ents sn rs (zero_val _) ctx
        (.inr (.inr (.inr (.inr (.inl Hty3)))))
        (fun _ => ⟨Hteq, Hterm⟩)
        (.inr Hrole) (Hwf.2.2.1)
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun _ Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      $$ [$Hphys Hm] as %err %s1 %dropped %c1 ⟨Hphys, %Hres, Herrn⟩
    · iapply msgIn_nonprop (by rw [Hty]; w32_ne) $$ Hm
    obtain ⟨rfl, rfl, Hs1⟩ := candidateStepResult_noop _ _ _ _ _ _ _ _ Hty3 Hres
    rw [Hs1]
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    iapply HΦ $$ %interface.nil %s
    iframe Hphys
    ipureintro
    exact ⟨Hwf, ⟨[], fun _ Hin => absurd Hin List.not_mem_nil, StepCD.frame (.refl _) (RFrame.refl _)⟩, rfl,
      keep_frame rfl rfl rfl rfl rfl⟩

end StepProof

end branches

end EtcdGrove
end Perennial
