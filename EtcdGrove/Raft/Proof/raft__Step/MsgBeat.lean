/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgBeat.v.

`Step`'s `MsgBeat` branch, in its own file so that it checks in parallel with the
others. Proof structure, not specification: no `Module Type`, no `Parameter`; only
`Proof/raft__Step.lean` may import this module.

Lean notes: the branch lemma takes the callee specs (Rocq's functor argument
`P : STEP_POSTULATES`) as its first argument `_P : raft.Step.Postulates`, and Rocq's
section variable `cfg` as its second.
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

/-- `MsgBeat` is local (`m.Term = 0`: `tickHeartbeat` builds it), so the term preamble
is skipped; it is none of the type switch's four cases, so `r.step(m)` runs.
`stepFollower` and `stepCandidate` have no arm for it (`Step.refl`); `stepLeader` runs
`bcastHeartbeat`, whose heartbeats are `Step.beat`'s (`leader_beat_step`). -/
theorem wp_Step_MsgBeat (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message) :
    m.Type' = MsgBeat →
    m.Term' = W64 0 →
    id ∈ cfg →
    NStateWf s →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhys cfg r id s }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhys cfg r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜Step cfg id (toPState s) [] (toPState s')⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ }} := by
  intro Hty Hterm Hcfg Hwf
  wp_start as Hphys
  iNamed Hphys
  wp_alloc r_ptr as r; wp_pures; wp_alloc m_ptr as m; wp_pures; wp_load; wp_pures
  wp_apply _P.traceReceiveMessage
  wp_pures; wp_load; wp_pures
  -- `m.Term = 0` (a local message), so the term preamble is skipped
  rw [decide_eq_true Hterm]
  wp_pures; wp_load; wp_pures
  -- the type switch: none of its four cases, so `r.step(m)`
  rw [Hty]
  wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures; iclear r m
  wp_apply raft.wp_load_step $$ Hphys as Hphys
  have Hty3 : m.Type' = MsgBeat ∨ m.Type' = MsgAppResp ∨ m.Type' = MsgHeartbeatResp :=
    .inl Hty
  rw [show s.stepfn = stepFuncOf s.role from Hwf]
  have Hsnap0 : ∀ (P : IProp GF), ⊢ (⌜m.Type' = MsgSnap⌝ -∗ P : IProp GF) := fun P => by
    iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
  cases Hrole : s.role
  · -- Follower: no `MsgBeat` arm
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
    exact ⟨Hwf, .refl _, rfl⟩
  · -- Candidate: no `MsgBeat` arm either
    simp only [stepFuncOf]
    wp_apply _P.stepCandidate cfg r id s m [] (zero_val _) []
        (.inr (.inr (.inr (.inr (.inl Hty3)))))
        (fun Hc => by
          exfalso; rw [Hty] at Hc
          rcases Hc with Hc | Hc | Hc | Hc <;> exact absurd Hc (by w32_ne))
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
    exact ⟨Hwf, .refl _, rfl⟩
  · -- Leader: `bcastHeartbeat`
    simp only [stepFuncOf]
    wp_apply _P.stepLeader cfg r id s m [] (.inr (.inl Hty)) Hrole Hcfg
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by
          exfalso; rw [Hty] at Hc
          rcases Hc with Hc | ⟨Hc, -⟩ <;> exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      $$ [$Hphys] as %err %s' %dropped ⟨Hphys, %Hres, Herrn, -⟩
    · isplitl []
      · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
      · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
    wp_pures; wp_alloc err_ptr as err; wp_pures; wp_store; wp_pures; wp_load; wp_pures
    obtain ⟨rfl, Hwf', Hstep⟩ := leader_beat_step cfg id s m [] dropped s' Hrole Hty Hwf Hres
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_pures; iclear err
    iapply HΦ $$ %interface.nil %s'
    iframe Hphys
    ipureintro
    exact ⟨Hwf', Hstep, rfl⟩
  · -- PreCandidate (2026-10-04), as a candidate: no `MsgBeat` arm either
    simp only [stepFuncOf]
    wp_apply _P.stepCandidate cfg r id s m [] (zero_val _) []
        (.inr (.inr (.inr (.inr (.inl Hty3)))))
        (fun Hc => by
          exfalso; rw [Hty] at Hc
          rcases Hc with Hc | Hc | Hc | Hc <;> exact absurd Hc (by w32_ne))
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
    exact ⟨Hwf, .refl _, rfl⟩

end StepProof

end branches

end EtcdGrove
end Perennial
