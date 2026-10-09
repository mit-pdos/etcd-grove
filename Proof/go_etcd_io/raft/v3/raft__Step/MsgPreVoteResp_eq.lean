/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgPreVoteResp_eq.v.

One term case of `Step`'s `MsgPreVoteResp` branch (2026-10-04): the incoming term is
the node's own. In its own file so that it checks in parallel with the others;
`MsgPreVoteResp.lean` combines them. Proof structure, not specification: no
`Module Type`, no `Parameter`; only files in this directory may import it.

Lean notes:
* The branch lemma takes the callee specs (Rocq's functor argument
  `P : STEP_POSTULATES`) as its first argument `_P : raft.Step.Postulates`, and Rocq's
  section variable `cfg` as its second.
* Rocq's `Local Ltac`s `recv_elem` (membership in a `recv` list built from `++` and
  singletons), `wp_load_step` (`raft.wp_load_step` on `"Hphys"`) and `ne_ty`
  (`bool_decide (m.Type = c) = false` by `w32_ne`) are not ported. The four role
  cases of `r.step(m)` (shared by `MsgPreVoteResp_gt.lean` and `MsgPreVoteResp_eq.lean`)
  are the local macro `prevote_resp_dispatch`.
-/
module

public import Proof.go_etcd_io.raft.v3.raft__Step.prevote_lemmas

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

set_option hygiene false in
/-- `r.step(m)` on a `MsgPreVoteResp` at the node's own term, by role (Rocq: the four
role cases, each with `wp_load_step`): `stepFollower` and `stepLeader` have no arm for
it; `stepCandidate` ignores it at a candidate and tallies it at a pre-candidate
(`candidateStepResult_prevoteresp`). Consumes nothing. Uses `Hphys`, `HΦ`, `Hty`,
`Hwf`, `Hcfg`, `Hnw`. -/
local macro "prevote_resp_dispatch" : tactic =>
  `(tactic| (
    wp_apply Perennial.EtcdGrove.raft.wp_load_step $$ Hphys as Hphys
    rw [show s.stepfn = stepFuncOf s.role from Hwf.1]
    cases Hrole : s.role
    · -- Follower: no arm
      simp only [stepFuncOf]
      wp_apply _P.stepFollower cfg r id s m [] (zero_val _) []
          (.inr (.inr (.inr (.inr (.inr (.inr Hty))))))
          (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
          (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
          (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        $$ [Hphys] as %err %s1 %dropped ⟨Hphys, %Hres, Herrn⟩
      · iframe Hphys
        isplitl []
        · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
        · iintro %Hc; exfalso; rw [Hty] at Hc
          rcases Hc with Hc | Hc <;> exact absurd Hc (by w32_ne)
      obtain ⟨rfl, rfl⟩ := followerStepResult_prevoteresp _ _ _ _ _ _ _ Hty Hres
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Herrn with %Herrn
      subst Herrn
      wp_auto
      iapply HΦ $$ %interface.nil %_
      iframe Hphys
      ipureintro
      exact ⟨Hwf, ⟨[], fun _ h => absurd h List.not_mem_nil, .refl _⟩, rfl,
      RespStep.refl _ _, keep_frame rfl rfl rfl rfl rfl⟩
    · -- Candidate: `myVoteRespType` is `MsgVoteResp`; a stale pre-vote response is
      -- ignored
      simp only [stepFuncOf]
      wp_apply _P.stepCandidate cfg r id s m [] (zero_val _) []
          (.inr (.inr (.inr (.inr (.inr (.inr Hty))))))
          (fun Hc => by
            exfalso; rw [Hty] at Hc
            rcases Hc with Hc | Hc | Hc | Hc <;> exact absurd Hc (by w32_ne))
          (.inl Hrole) Hcfg
          (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
          (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
          (fun Hp _ => Hnw Hp)
        $$ [Hphys] as %err %s1 %dropped ⟨Hphys, %Hres, Herrn⟩
      · iframe Hphys
        isplitl []
        · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
        · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
      obtain ⟨rfl, Hwf1, Hst, Hresp, Hft⟩ :=
        candidateStepResult_prevoteresp cfg _ _ _ _ _ _ _ Hty (.inl Hrole) Hcfg Hnw Hwf Hres
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Herrn with %Herrn
      subst Herrn
      wp_auto
      iapply HΦ $$ %interface.nil %s1
      iframe Hphys
      ipureintro
      exact ⟨Hwf1, ⟨[], fun _ h => absurd h List.not_mem_nil, Hst⟩, rfl, Hresp, Hft⟩
    · -- Leader: no arm
      simp only [stepFuncOf]
      wp_apply _P.stepLeader cfg r id s m [] (.inr (.inr (.inr (.inr (.inr (.inr (.inr Hty)))))))
          Hrole Hcfg
          (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
          (fun Hc => by
            exfalso; rw [Hty] at Hc
            rcases Hc with Hc | ⟨Hc, -⟩ <;> exact absurd Hc (by w32_ne))
          (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        $$ [Hphys] as %err %s' %dropped ⟨Hphys, %Hres, Herrn, -⟩
      · iframe Hphys
        isplitl []
        · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
        · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
      obtain ⟨rfl, rfl⟩ := leaderStepResult_prevoteresp cfg _ _ _ _ _ _ Hty Hres
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Herrn with %Herrn
      subst Herrn
      wp_auto
      iapply HΦ $$ %interface.nil %_
      iframe Hphys
      ipureintro
      exact ⟨Hwf, ⟨[], fun _ h => absurd h List.not_mem_nil, .refl _⟩, rfl,
      RespStep.refl _ _, keep_frame rfl rfl rfl rfl rfl⟩
    · -- PreCandidate: the pre-vote tally
      simp only [stepFuncOf]
      wp_apply _P.stepCandidate cfg r id s m [] (zero_val _) []
          (.inr (.inr (.inr (.inr (.inr (.inr Hty))))))
          (fun Hc => by
            exfalso; rw [Hty] at Hc
            rcases Hc with Hc | Hc | Hc | Hc <;> exact absurd Hc (by w32_ne))
          (.inr Hrole) Hcfg
          (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
          (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
          (fun Hp _ => Hnw Hp)
        $$ [Hphys] as %err %s1 %dropped ⟨Hphys, %Hres, Herrn⟩
      · iframe Hphys
        isplitl []
        · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
        · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
      obtain ⟨rfl, Hwf1, Hst, Hresp, Hft⟩ :=
        candidateStepResult_prevoteresp cfg _ _ _ _ _ _ _ Hty (.inr Hrole) Hcfg Hnw Hwf Hres
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Herrn with %Herrn
      subst Herrn
      wp_auto
      iapply HΦ $$ %interface.nil %s1
      iframe Hphys
      ipureintro
      exact ⟨Hwf1, ⟨[], fun _ h => absurd h List.not_mem_nil, Hst⟩, rfl, Hresp, Hft⟩))

/-- `MsgPreVoteResp` at `m.Term = r.Term`: the preamble does nothing and the type
switch's default arm runs `r.step(m)`. Only a pre-candidate acts on it (`stepCandidate`
with `myVoteRespType = MsgPreVoteResp`: the tally, then `campaign(campaignElection)` on
a win, `becomeFollower` on a loss); everyone else ignores it. Nothing is received by
the protocol: `Step.refl`, `Step.abandon` or `Step.campaign`
(`step_prevoteRespResult`). -/
theorem wp_Step_MsgPreVoteResp_eq (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) :
    m.Type' = MsgPreVoteResp →
    m.To' = id →
    m.Term' ≠ W64 0 →
    -- this file: the same term
    m.Term' = s.term →
    (s.role = .preCandidate → uint.Z s.term + 1 < 2 ^ 64) →
    id ∈ cfg →
    NStateWf s →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhys cfg r id s }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhys cfg r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absMsg .preVoteResp m ents) ∧
            Step cfg id (toPState s) recv (toPState s')⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hresp" ∷ ⌜RespStep m s s'⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ }} := by
  intro Hty Hto Hterm Hteq Hnw Hcfg Hwf
  wp_start as Hphys
  iNamed Hphys
  wp_auto
  wp_apply _P.traceReceiveMessage
  -- `m.Term ≠ 0`, so the first arm of the term preamble is skipped
  rw [decide_eq_false Hterm]
  wp_auto
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  rw [decide_eq_false (show ¬ uint.Z s.term < uint.Z m.Term' by rw [Hteq]; omega)]
  wp_auto
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  rw [decide_eq_false (show ¬ uint.Z m.Term' < uint.Z s.term by rw [Hteq]; omega)]
  wp_auto
  -- the type switch: none of its four cases, so `r.step(m)`
  rw [Hty]
  wp_auto
  prevote_resp_dispatch

end StepProof

end branches

end EtcdGrove
end Perennial
