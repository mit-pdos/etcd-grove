/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgPreVoteResp_gt.v.

One term case of `Step`'s `MsgPreVoteResp` branch (2026-10-04): the incoming term is
higher. In its own file so that it checks in parallel with the others;
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
    rw [show s.stepfn = stepFuncOf s.role from Hwf]
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
      keep_frame rfl rfl rfl rfl rfl⟩
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
          (fun _ _ => Hnw)
        $$ [Hphys] as %err %s1 %dropped ⟨Hphys, %Hres, Herrn⟩
      · iframe Hphys
        isplitl []
        · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
        · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
      obtain ⟨rfl, Hwf1, Hst, Hft⟩ :=
        candidateStepResult_prevoteresp cfg _ _ _ _ _ _ _ Hty (.inl Hrole) Hcfg Hnw Hwf Hres
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Herrn with %Herrn
      subst Herrn
      wp_auto
      iapply HΦ $$ %interface.nil %s1
      iframe Hphys
      ipureintro
      exact ⟨Hwf1, ⟨[], fun _ h => absurd h List.not_mem_nil, Hst⟩, rfl, Hft⟩
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
      keep_frame rfl rfl rfl rfl rfl⟩
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
          (fun _ _ => Hnw)
        $$ [Hphys] as %err %s1 %dropped ⟨Hphys, %Hres, Herrn⟩
      · iframe Hphys
        isplitl []
        · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
        · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
      obtain ⟨rfl, Hwf1, Hst, Hft⟩ :=
        candidateStepResult_prevoteresp cfg _ _ _ _ _ _ _ Hty (.inr Hrole) Hcfg Hnw Hwf Hres
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Herrn with %Herrn
      subst Herrn
      wp_auto
      iapply HΦ $$ %interface.nil %s1
      iframe Hphys
      ipureintro
      exact ⟨Hwf1, ⟨[], fun _ h => absurd h List.not_mem_nil, Hst⟩, rfl, Hft⟩))

/-- `MsgPreVoteResp` with `m.Term > r.Term`. A *granted* one does not step the node down
(raft.go:1104: it carries the pre-candidate's future term): straight to `r.step(m)`, as
at the current term. A *rejecting* one does -- `becomeFollower(m.Term, None)`, one
`Step.higherTerm` (not `fromLeader`) -- and then `stepFollower` has no arm for it. -/
theorem wp_Step_MsgPreVoteResp_gt (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) :
    m.Type' = MsgPreVoteResp →
    m.To' = id →
    m.Term' ≠ W64 0 →
    -- this file: the incoming term is strictly higher
    uint.Z s.term < uint.Z m.Term' →
    uint.Z s.term + 1 < 2 ^ 64 →
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
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ }} := by
  intro Hty Hto Hterm Hgt Hnw Hcfg Hwf
  have Hn17 : decide (m.Type' = W32 17) = false := decide_eq_false (by rw [Hty]; w32_ne)
  have Hn5 : decide (m.Type' = W32 5) = false := decide_eq_false (by rw [Hty]; w32_ne)
  have Hn3 : decide (m.Type' = W32 3) = false := decide_eq_false (by rw [Hty]; w32_ne)
  have Hn8 : decide (m.Type' = W32 8) = false := decide_eq_false (by rw [Hty]; w32_ne)
  have Hn7 : decide (m.Type' = W32 7) = false := decide_eq_false (by rw [Hty]; w32_ne)
  have Hy18 : decide (m.Type' = W32 18) = true := decide_eq_true Hty
  wp_start as Hphys
  iNamed Hphys
  wp_auto
  wp_apply _P.traceReceiveMessage
  -- `m.Term ≠ 0`, so the first arm of the term preamble is skipped
  rw [decide_eq_false Hterm]
  wp_auto
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  rw [decide_eq_true Hgt]
  wp_auto
  -- `(Type == MsgVote) || (Type == MsgPreVote)`: both false
  rw [Hn5]
  wp_auto
  rw [Hn17]
  wp_auto
  -- the step-down switch: not `MsgPreVote`; `MsgPreVoteResp`, and `!Reject` decides
  rw [Hn17]
  wp_auto
  rw [Hy18]
  wp_auto
  cases Hrej : m.Reject'
  · -- granted: no step-down; `r.step(m)` in the current role
    wp_auto
    rw [Hty]
    wp_auto
    prevote_resp_dispatch
  -- rejected: step down to the higher term, no leader
  wp_auto
  wp_apply raft.wp_load_id $$ Hphys as Hphys
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  wp_raft_log
  rw [Hn3]
  wp_auto
  rw [Hn8]
  wp_auto
  rw [Hn7]
  wp_auto
  wp_apply _P.becomeFollower cfg r id s m.Term' (W64 0) $$ [$Hphys] as %pvs Hphys
  -- the type switch: none of its cases, so `r.step(m)`
  rw [Hty]
  wp_auto
  wp_apply raft.wp_load_step $$ Hphys as Hphys
  have Hsd : Step cfg id (toPState s) [absMsg .preVoteResp m ents]
      (toPState (becomeFollower s m.Term' (W64 0))) := by
    rw [toPState_becomeFollower]
    exact Step.higherTerm (absMsg .preVoteResp m ents) (toPState s) Hgt Hto
      (by simp [absMsg, absMsgFrom, fromLeader])
  rw [show ({ becomeFollower s m.Term' (W64 0) with prvals := pvs } : NState).stepfn =
    functions stepFollower [] from rfl]
  wp_apply _P.stepFollower cfg r id _ m [] (zero_val _) []
      (.inr (.inr (.inr (.inr (.inr (.inr Hty))))))
      (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
    $$ [$Hphys] as %err %s1 %dropped ⟨Hphys, %Hres, Herrn⟩
  · isplitl []
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
  refine ⟨rfl, ⟨[absMsg .preVoteResp m ents], fun _ h => List.mem_singleton.1 h, ?_⟩, rfl,
    stepdown_frame (by rw [Hty]; w32_ne) (Int.le_of_lt Hgt) rfl rfl rfl rfl rfl⟩
  rw [toPState_prvals_nl (becomeFollower s m.Term' (W64 0)) pvs (by simp [becomeFollower])]
  exact Hsd

end StepProof

end branches

end EtcdGrove
end Perennial
