/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgHeartbeatResp_eq.v.

The current-term case of `Step`'s `MsgHeartbeatResp` branch, in its own file so that
it checks in parallel with the other term cases -- see `MsgHeartbeatResp.lean`, which
combines them. Proof structure, not specification: no `Module Type`, no `Parameter`;
only files in this directory may import it.

Lean notes:
* The branch lemma takes the callee specs (Rocq's functor argument
  `P : STEP_POSTULATES`) as its first argument `_P : raft.Step.Postulates`, and Rocq's
  section variable `cfg` as its second.
* Rocq's `Local Ltac`s `recv_elem`, `wp_load_step`, `ne_ty` are not ported
  (proof-side helpers; the proof porter may write Lean macros or inline them).
-/
import EtcdGrove.Raft.Proof.raft__Step.resp_lemmas

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section branches
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [AllG GF]

namespace StepProof

/-- `MsgHeartbeatResp` at `m.Term = r.Term`: the preamble does nothing and the type
switch's default arm runs `r.step(m)`. `stepFollower` and `stepCandidate` have no arm
for it (`Step.refl`); `stepLeader` may `sendAppend` to the peer, which is
`Step.sendApps` (`leader_hbresp_step`). The empty `Context` is what keeps `stepLeader`
out of the read-only code. -/
theorem wp_Step_MsgHeartbeatResp_eq (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) :
    m.Type' = MsgHeartbeatResp →
    m.To' = id →
    m.Term' ≠ W64 0 →
    m.Term' = s.term →
    m.From' ≠ W64 0 →
    m.From' ≠ id →
    id ∈ cfg →
    NStateWf s →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhys cfg r id s ∗
        "#Hctx0" ∷ m.Context' ↦*□ ([] : List w8) }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhys cfg r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absMsg .heartbeatResp m ents) ∧
            Step cfg id (toPState s) recv (toPState s')⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ }} := by
  intro Hty Hto Hterm Hteq Hfnz Hfid Hcfg Hwf
  have Hty3 : m.Type' = MsgBeat ∨ m.Type' = MsgAppResp ∨ m.Type' = MsgHeartbeatResp :=
    .inr (.inr Hty)
  wp_start as Hphys
  iNamed Hphys
  wp_alloc r_ptr as r; wp_pures; wp_alloc m_ptr as m; wp_pures; wp_load; wp_pures
  wp_apply _P.traceReceiveMessage
  wp_pures; wp_load; wp_pures
  rw [decide_eq_false Hterm]
  wp_pures; wp_load; wp_load; wp_pures
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  wp_pures
  rw [decide_eq_false (show ¬ (uint.Z s.term < uint.Z m.Term') by rw [Hteq]; omega)]
  wp_pures; wp_load; wp_load; wp_pures
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  wp_pures
  rw [decide_eq_false (show ¬ (uint.Z m.Term' < uint.Z s.term) by rw [Hteq]; omega)]
  wp_pures; wp_load; wp_pures
  -- the type switch: none of its four cases, so `r.step(m)`
  rw [Hty]
  wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures; iclear r m
  wp_apply raft.wp_load_step $$ Hphys as Hphys
  rw [show s.stepfn = stepFuncOf s.role from Hwf]
  have Hsnap0 : ∀ (P : IProp GF), ⊢ (⌜m.Type' = MsgSnap⌝ -∗ P : IProp GF) := fun P => by
    iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
  cases Hrole : s.role
  · -- Follower: no `MsgHeartbeatResp` arm
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
    wp_pures; wp_alloc err_ptr as err; wp_pures; wp_store; wp_pures; wp_load; wp_pures
    obtain ⟨rfl, Hs1⟩ := followerStepResult_noop _ _ _ _ _ _ _ Hty3 Hres
    rw [Hs1]
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_pures; iclear err
    iapply HΦ $$ %interface.nil %s
    iframe Hphys
    ipureintro
    exact ⟨Hwf, ⟨[], fun _ Hin => absurd Hin List.not_mem_nil, .refl _⟩, rfl⟩
  · -- Candidate: no `MsgHeartbeatResp` arm either
    simp only [stepFuncOf]
    wp_apply _P.stepCandidate cfg r id s m [] (zero_val _) []
        (.inr (.inr (.inr (.inr (.inl Hty3)))))
        (fun _ => Hteq)
        (.inl Hrole) Hcfg
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun _ Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      $$ [$Hphys] as %err %s1 %dropped ⟨Hphys, %Hres, Herrn⟩
    · isplitl []
      · iapply Hsnap0
      · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
    wp_pures; wp_alloc err_ptr as err; wp_pures; wp_store; wp_pures; wp_load; wp_pures
    obtain ⟨rfl, Hs1⟩ := candidateStepResult_noop _ _ _ _ _ _ _ _ Hty3 Hres
    rw [Hs1]
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_pures; iclear err
    iapply HΦ $$ %interface.nil %s
    iframe Hphys
    ipureintro
    exact ⟨Hwf, ⟨[], fun _ Hin => absurd Hin List.not_mem_nil, .refl _⟩, rfl⟩
  · -- Leader: `sendAppend` to a peer that is behind
    simp only [stepFuncOf]
    wp_apply _P.stepLeader cfg r id s m [] (.inr (.inr (.inl Hty))) Hrole Hcfg
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun _ => Hfid)
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      $$ [$Hphys] as %err %s' %dropped ⟨Hphys, %Hres, Herrn, -⟩
    · isplitl []
      · iintro _; iexact Hctx0
      · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
    wp_pures; wp_alloc err_ptr as err; wp_pures; wp_store; wp_pures; wp_load; wp_pures
    obtain ⟨rfl, Hwf', Hstep⟩ := leader_hbresp_step cfg id s m [] dropped s' Hrole Hty Hwf Hres
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_pures; iclear err
    iapply HΦ $$ %interface.nil %s'
    iframe Hphys
    ipureintro
    exact ⟨Hwf', ⟨[], fun _ Hin => absurd Hin List.not_mem_nil, Hstep⟩, rfl⟩
  · -- PreCandidate (2026-10-04), as a candidate: no `MsgHeartbeatResp` arm either
    simp only [stepFuncOf]
    wp_apply _P.stepCandidate cfg r id s m [] (zero_val _) []
        (.inr (.inr (.inr (.inr (.inl Hty3)))))
        (fun _ => Hteq)
        (.inr Hrole) Hcfg
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun _ Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      $$ [$Hphys] as %err %s1 %dropped ⟨Hphys, %Hres, Herrn⟩
    · isplitl []
      · iapply Hsnap0
      · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
    wp_pures; wp_alloc err_ptr as err; wp_pures; wp_store; wp_pures; wp_load; wp_pures
    obtain ⟨rfl, Hs1⟩ := candidateStepResult_noop _ _ _ _ _ _ _ _ Hty3 Hres
    rw [Hs1]
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_pures; iclear err
    iapply HΦ $$ %interface.nil %s
    iframe Hphys
    ipureintro
    exact ⟨Hwf, ⟨[], fun _ Hin => absurd Hin List.not_mem_nil, .refl _⟩, rfl⟩

end StepProof

end branches

end EtcdGrove
end Perennial
