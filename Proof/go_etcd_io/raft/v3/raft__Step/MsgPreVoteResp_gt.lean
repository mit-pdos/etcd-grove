/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgPreVoteResp_gt.v.

One term case of `Step`'s `MsgPreVoteResp` branch (2026-10-04): the incoming term is
higher. In its own file so that it checks in parallel with the others;
`MsgPreVoteResp.lean` combines them. Proof structure, not specification: no
`Module Type`, no `Parameter`; only files in this directory may import it.

Lean notes:
* The branch lemma takes the callee specs (Rocq's functor argument
  `P : STEP_POSTULATES`) as its first argument `_P : raft.Step.Postulates`, and Rocq's
  section variable `c` as its second.
* Rocq's `Local Ltac`s `recv_elem` (membership in a `recv` list built from `++` and
  singletons), `wp_load_step` (`raft.wp_load_stepC` on `"Hphys"`) and `ne_ty`
  (`bool_decide (m.Type = c) = false` by `w32_ne`) are not ported. The four role
  cases of `r.step(m)` (shared by `MsgPreVoteResp_gt.lean` and `MsgPreVoteResp_eq.lean`)
  are the macro `prevote_resp_dispatch` (`ElectionLemmas.lean`).

raft v3.7 (2026-10-15, stage R4 phase 3): the message is a pointer `ml` with `msgIn ml □ ⟨m, ents,
sn, ctx, rs⟩`, read by its getters (`wp_get`/`wp_gets`, `ElectionLemmas.lean`, by `PB`; `Step`
first checks `m != nil`, `msgPtsC_nn`) and handed to `r.step` whole (the `stepX` specs take
`msgIn`; their `MsgSnap` premise is pure). The callees now see the message's entries and context
(the old proof passed `[]`), so the pre-vote lemmas (`followerStepResult_prevoteresp` etc.,
`prevote_lemmas.lean`) are stated at any `cl`/`ctx`.
-/
module

public import Proof.go_etcd_io.raft.v3.raft__Step.prevote_lemmas
public import Proof.go_etcd_io.raft.v3.raft__Step.ElectionLemmas

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

set_option maxHeartbeats 2000000 in
/-- `MsgPreVoteResp` with `m.Term > r.Term`. A *granted* one does not step the node down
(raft.go:1104: it carries the pre-candidate's future term): straight to `r.step(m)`, as
at the current term. A *rejecting* one does -- `becomeFollower(m.Term, None)`, one
`StepC.higherTerm` (not `fromLeader`) -- and then `stepFollower` has no arm for it. -/
theorem wp_Step_MsgPreVoteResp_gt (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (PB : raft.Step.PbPostulates (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc) :
    m.Type' = MsgPreVoteResp →
    m.To' = id →
    m.Term' ≠ W64 0 →
    -- this file: the incoming term is strictly higher
    uint.Z s.term < uint.Z m.Term' →
    (s.role = .preCandidate → uint.Z s.term + 1 < 2 ^ 64) →
    NStateWf s →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
        "Hm" ∷ msgIn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absMsg .preVoteResp m ents) ∧
            StepCD c id B m s recv s'⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hresp" ∷ ⌜RespStep m s s'⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ }} := by
  intro Hty Hto Hterm Hgt Hnw Hwf
  have Hn17 : decide (m.Type' = W32 17) = false := decide_eq_false (by rw [Hty]; w32_ne)
  have Hn5 : decide (m.Type' = W32 5) = false := decide_eq_false (by rw [Hty]; w32_ne)
  have Hn3 : decide (m.Type' = W32 3) = false := decide_eq_false (by rw [Hty]; w32_ne)
  have Hn8 : decide (m.Type' = W32 8) = false := decide_eq_false (by rw [Hty]; w32_ne)
  have Hn7 : decide (m.Type' = W32 7) = false := decide_eq_false (by rw [Hty]; w32_ne)
  have Hy18 : decide (m.Type' = W32 18) = true := decide_eq_true Hty
  wp_start as ⟨Hphys, Hm⟩
  icases msgPtsC_nn _ _ _ _ _ $$ Hm with ⟨%Hnn, Hm⟩
  try wp_auto
  wp_gets
  rw [decide_eq_false Hnn]
  try wp_auto
  wp_gets
  wp_apply _P.traceReceiveMessage
  try wp_auto
  wp_gets
  -- `m.Term ≠ 0`, so the first arm of the term preamble is skipped
  wp_gets
  rw [decide_eq_false Hterm]
  try wp_auto
  wp_gets
  wp_apply raft.wp_load_TermC $$ Hphys as Hphys
  wp_gets
  rw [decide_eq_true Hgt]
  try wp_auto
  -- `(Type == MsgVote) || (Type == MsgPreVote)`: both false
  wp_gets
  rw [Hn5]
  try wp_auto
  wp_gets
  rw [Hn17]
  try wp_auto
  -- the step-down switch: not `MsgPreVote`; `MsgPreVoteResp`, and `!Reject` decides
  wp_gets
  rw [Hn17]
  try wp_auto
  wp_gets
  rw [Hy18]
  try wp_auto
  wp_gets
  -- (stage R4) `GetReject`'s result is a projection of the message's record
  rw [show ({ msg := m, ents := ents, snap := sn, ctx := ctx, resps := rs } : MsgSt).msg.Reject' =
    m.Reject' from rfl]
  cases Hrej : m.Reject'
  · -- granted: no step-down; `r.step(m)` in the current role
    try wp_auto
    wp_gets
    rw [Hty]
    try wp_auto
    prevote_resp_dispatch
  -- rejected: step down to the higher term, no leader
  try wp_auto
  wp_gets
  wp_apply raft.wp_load_idC $$ Hphys as Hphys
  wp_gets
  wp_apply raft.wp_load_TermC $$ Hphys as Hphys
  wp_gets
  wp_raft_logC
  wp_gets
  rw [Hn3]
  try wp_auto
  wp_gets
  rw [Hn8]
  try wp_auto
  wp_gets
  rw [Hn7]
  try wp_auto
  wp_gets
  wp_apply _P.becomeFollower c r id s m.Term' (W64 0) (Int.le_of_lt Hgt) $$ [$Hphys] as %pvs Hphys
  -- the type switch: none of its cases, so `r.step(m)`
  wp_gets
  rw [Hty]
  try wp_auto
  wp_gets
  wp_apply raft.wp_load_stepC $$ Hphys as Hphys
  have Hsd : StepCF c id (toPState s) [absMsg .preVoteResp m ents]
      (toPState (becomeFollower s m.Term' (W64 0))) := by
    rw [toPState_becomeFollower]
    exact StepCF.higherTerm (absMsg .preVoteResp m ents) (toPState s) Hgt Hto
      (by simp [absMsg, absMsgFrom, fromLeader])
  wp_gets
  rw [show ({ becomeFollower s m.Term' (W64 0) with prvals := pvs } : NState).stepfn =
    functions stepFollower [] from rfl]
  wp_gets
  have Hnp : ¬ m.Type' = MsgProp := by rw [Hty]; w32_ne
  wp_apply _P.stepFollower c ∅ r id _ ml m ents sn rs (zero_val _) ctx
      (.inr (.inr (.inr (.inr (.inr (.inr (.inl Hty)))))))
      (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      (fun Hc => by exfalso; rcases Hc with Hc | Hc <;> rw [Hty] at Hc <;> exact absurd Hc (by w32_ne))
      (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
    $$ [$Hphys Hm] as %err %s1 %dropped %c1 ⟨Hphys, %Hres, Herrn⟩
  · rw [ite_eq_right Hnp]; iexact Hm
  obtain ⟨rfl, rfl, rfl⟩ := followerStepResult_prevoteresp _ _ _ _ _ _ _ _ _ Hty Hres
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Herrn with %Herrn
  subst Herrn
  try wp_auto
  iapply HΦ $$ %interface.nil %_
  iframe Hphys
  ipureintro
  refine ⟨⟨rfl, rfl⟩, ⟨[absMsg .preVoteResp m ents], fun _ h => List.mem_singleton.1 h,
    StepCD.frame ?_ (by rframe)⟩, rfl,
    ⟨fun h => by rcases h with h | h <;> rw [Hty] at h <;> exact absurd h (by w32_ne),
     fun _ => ⟨.inl (Int.le_max_right _ _), fun h => absurd h (by simp [becomeFollower])⟩⟩,
    stepdown_frame (by rw [Hty]; w32_ne) (Int.le_of_lt Hgt) rfl rfl rfl rfl rfl⟩
  rw [toPState_prvals_nl (becomeFollower s m.Term' (W64 0)) pvs (by simp [becomeFollower])]
  exact Hsd

end StepProof

end branches

end EtcdGrove
end Perennial
