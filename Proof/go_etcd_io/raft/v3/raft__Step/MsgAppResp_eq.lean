/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgAppResp_eq.v.

The current-term case of `Step`'s `MsgAppResp` branch, in its own file so that it
checks in parallel with the other term cases -- see `MsgAppResp.lean`, which combines
them. Proof structure, not specification: no `Module Type`, no `Parameter`; only files
in this directory may import it.

Lean notes:
* The branch lemma takes the callee specs (Rocq's functor argument
  `P : STEP_POSTULATES`) as its first argument `_P : raft.Step.Postulates`, and Rocq's
  section variable `cfg` as its second.
* Rocq's `Local Ltac`s `recv_elem`, `wp_load_step`, `ne_ty` are not ported
  (proof-side helpers; the proof porter may write Lean macros or inline them).
-/
module

public import Proof.go_etcd_io.raft.v3.raft__Step.resp_lemmas

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

/-- `MsgAppResp` at `m.Term = r.Term`: the preamble does nothing and the type switch's
default arm runs `r.step(m)`. `stepFollower` and `stepCandidate` have no arm for it
(`Step.refl`); `stepLeader` is the replication path, whose `LeaderStepResult` becomes
`Step.appResp`/`Step.commit`/`Step.sendApps` (`leader_appresp_step`). -/
theorem wp_Step_MsgAppResp_eq (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) :
    m.Type' = MsgAppResp →
    m.To' = id →
    m.Term' ≠ W64 0 →
    m.Term' = s.term →
    m.From' ≠ W64 0 →
    (m.Reject' = true → m.From' ≠ id) →
    id ∈ cfg →
    NStateWf s →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhys cfg r id s }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhys cfg r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absMsg .appResp m ents) ∧
            Step cfg id (toPState s) recv (toPState s')⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ }} := by
  intro Hty Hto Hterm Hteq Hfnz Hrej Hcfg Hwf
  have Hty3 : m.Type' = MsgBeat ∨ m.Type' = MsgAppResp ∨ m.Type' = MsgHeartbeatResp :=
    .inr (.inl Hty)
  wp_start as Hphys
  iNamed Hphys
  wp_auto
  wp_apply _P.traceReceiveMessage
  rw [decide_eq_false Hterm]
  wp_auto
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  rw [decide_eq_false (show ¬ (uint.Z s.term < uint.Z m.Term') by rw [Hteq]; omega)]
  wp_auto
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  rw [decide_eq_false (show ¬ (uint.Z m.Term' < uint.Z s.term) by rw [Hteq]; omega)]
  wp_auto
  -- the type switch: none of its four cases, so `r.step(m)`
  rw [Hty]
  wp_auto
  wp_apply raft.wp_load_step $$ Hphys as Hphys
  rw [show s.stepfn = stepFuncOf s.role from Hwf.1]
  have Hsnap0 : ∀ (P : IProp GF), ⊢ (⌜m.Type' = MsgSnap⌝ -∗ P : IProp GF) := fun P => by
    iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
  cases Hrole : s.role
  · -- Follower: no `MsgAppResp` arm
    simp only [stepFuncOf]
    wp_apply _P.stepFollower cfg r id s m [] (zero_val _) []
        (.inr (.inr (.inr (.inr (.inl Hty3)))))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      $$ [$Hphys] as %err %s1 %dropped ⟨Hphys, %Hres, Herrn⟩
    · isplitl []
      · iapply Hsnap0
      · iintro %Hc; exfalso; rw [Hty] at Hc
        rcases Hc with Hc | Hc <;> exact absurd Hc (by w32_ne)
    obtain ⟨rfl, Hs1⟩ := followerStepResult_noop _ _ _ _ _ _ _ Hty3 Hres
    rw [Hs1]
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    iapply HΦ $$ %interface.nil %s
    iframe Hphys
    ipureintro
    exact ⟨Hwf, ⟨[], fun _ Hin => absurd Hin List.not_mem_nil, .refl _⟩, rfl,
      keep_frame rfl rfl rfl rfl rfl⟩
  · -- Candidate: no `MsgAppResp` arm either
    simp only [stepFuncOf]
    wp_apply _P.stepCandidate cfg r id s m [] (zero_val _) []
        (.inr (.inr (.inr (.inr (.inl Hty3)))))
        (fun _ => ⟨Hteq, Hterm⟩)
        (.inl Hrole) Hcfg
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun _ Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      $$ [$Hphys] as %err %s1 %dropped ⟨Hphys, %Hres, Herrn⟩
    · isplitl []
      · iapply Hsnap0
      · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
    obtain ⟨rfl, Hs1⟩ := candidateStepResult_noop _ _ _ _ _ _ _ _ Hty3 Hres
    rw [Hs1]
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    iapply HΦ $$ %interface.nil %s
    iframe Hphys
    ipureintro
    exact ⟨Hwf, ⟨[], fun _ Hin => absurd Hin List.not_mem_nil, .refl _⟩, rfl,
      keep_frame rfl rfl rfl rfl rfl⟩
  · -- Leader: the replication path
    simp only [stepFuncOf]
    wp_apply _P.stepLeader cfg r id s m [] (.inr (.inr (.inr (.inl Hty)))) Hrole Hcfg
        (fun _ => Hfnz)
        (fun Hc => by
          rcases Hc with Hc | ⟨-, Hc⟩
          · exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
          · exact Hrej Hc)
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      $$ [$Hphys] as %err %s' %dropped ⟨Hphys, %Hres, Herrn, -⟩
    · isplitl []
      · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
      · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
    obtain ⟨rfl, Hwf', ⟨recv, Hrecv, Hstep⟩, Hft⟩ :=
      leader_appresp_step cfg id s m [] ents dropped s' Hrole Hty Hto Hteq Hwf Hres
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
    wp_apply _P.stepCandidate cfg r id s m [] (zero_val _) []
        (.inr (.inr (.inr (.inr (.inl Hty3)))))
        (fun _ => ⟨Hteq, Hterm⟩)
        (.inr Hrole) Hcfg
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun _ Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      $$ [$Hphys] as %err %s1 %dropped ⟨Hphys, %Hres, Herrn⟩
    · isplitl []
      · iapply Hsnap0
      · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
    obtain ⟨rfl, Hs1⟩ := candidateStepResult_noop _ _ _ _ _ _ _ _ Hty3 Hres
    rw [Hs1]
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    iapply HΦ $$ %interface.nil %s
    iframe Hphys
    ipureintro
    exact ⟨Hwf, ⟨[], fun _ Hin => absurd Hin List.not_mem_nil, .refl _⟩, rfl,
      keep_frame rfl rfl rfl rfl rfl⟩

end StepProof

end branches

end EtcdGrove
end Perennial
