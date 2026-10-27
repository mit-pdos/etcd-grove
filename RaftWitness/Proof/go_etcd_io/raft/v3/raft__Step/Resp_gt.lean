/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_Resp_gt.v.

The higher-term case of `Step`'s `MsgAppResp` and `MsgHeartbeatResp` branches, for both
types at once (they take the same path through the preamble and reach no arm of
`stepFollower`), in its own file so that it checks in parallel with the other term
cases -- see `MsgAppResp.lean` and `MsgHeartbeatResp.lean`, which combine them. Proof
structure, not specification: no `Module Type`, no `Parameter`; only files in this
directory may import it.

Lean notes:
* The branch lemma takes the callee specs (Rocq's functor argument
  `P : STEP_POSTULATES`) as its first argument `_P : raft.Step.Postulates`, and Rocq's
  section variable `c` as its second.
* Rocq's `Local Ltac`s `recv_elem`, `ne_ty`, `wp_load_step` are not ported
  (proof-side helpers; the proof porter may write Lean macros or inline them).
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.raft__Step.resp_lemmas
public import RaftWitness.Proof.go_etcd_io.raft.v3.raft__Step.ReplLemmas

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
/-- `m.Term > r.Term` for a `MsgAppResp` or `MsgHeartbeatResp`: neither is `fromLeader`,
so the preamble runs `becomeFollower(m.Term, None)`; the type switch then reaches its
default arm, `r.step(m)`, which is `stepFollower` after the step-down, and
`stepFollower` has no arm for either type. One `StepC.higherTerm`. -/
theorem wp_Step_Resp_gt (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (_Q : raft.Step.ReplPbPostulates (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc)
    (ents : List EntryM) (ty : MsgType) :
    (m.Type' = MsgAppResp ∧ ty = .appResp) ∨
    (m.Type' = MsgHeartbeatResp ∧ ty = .heartbeatResp) →
    m.To' = id →
    m.Term' ≠ W64 0 →
    uint.Z s.term < uint.Z m.Term' →
    NStateWf s →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
        "Hm" ∷ msgIn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absMsg ty m ents) ∧
            StepCD c id B m s recv s'⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ }} := by
  intro Hty Hto Hterm Hgt Hwf
  have Hfl : fromLeader ty = false := by
    rcases Hty with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
  have Hty3 : m.Type' = MsgBeat ∨ m.Type' = MsgAppResp ∨ m.Type' = MsgHeartbeatResp ∨
    m.Type' = MsgCheckQuorum := by
    rcases Hty with ⟨Ht, _⟩ | ⟨Ht, _⟩
    · exact .inr (.inl Ht)
    · exact .inr (.inr (.inl Ht))
  wp_start as H
  iNamed H
  icases msgPtsC_nn _ _ _ _ _ $$ Hm with ⟨%Hnn, Hm⟩
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply _P.traceReceiveMessage
  try wp_auto
  wp_apply _Q.GetTerm.1 $$ [$Hm] as Hm
  rw [decide_eq_false Hterm]
  wp_auto
  wp_apply _Q.GetTerm.1 $$ [$Hm] as Hm
  wp_apply raft.wp_load_TermC $$ Hphys as Hphys
  rw [decide_eq_true Hgt]
  wp_auto
  rcases Hty with ⟨Hty, -⟩ | ⟨Hty, -⟩
  -- (2026-10-20) the reads by `wp_drive` (`ReplLemmas.lean`), which applies the step the next
  -- redex asks for instead of trying each getter and load in turn
  all_goals
    wp_drive _Q
    wp_raft_logC
    wp_drive _Q
    wp_apply _P.becomeFollower _ _ _ _ _ _ (by exact Int.le_of_lt Hgt) $$ [$Hphys] as %pvs Hphys
    try wp_auto
    wp_drive _Q
    wp_apply raft.wp_load_stepC $$ Hphys as Hphys
    rw [show ({ becomeFollower s m.Term' (W64 0) with prvals := pvs } : NState).stepfn =
      stepFuncOf .follower from rfl]
    simp only [stepFuncOf]
    wp_apply _P.stepFollower c ∅ r id { becomeFollower s m.Term' (W64 0) with prvals := pvs }
        ml m ents sn rs (zero_val _) ctx (.inr (.inr (.inr (.inr (.inl Hty3)))))
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
    iapply HΦ $$ %interface.nil %({ becomeFollower s m.Term' (W64 0) with prvals := pvs })
    iframe Hphys
    ipureintro
    refine ⟨⟨rfl, rfl⟩, ⟨[absMsg ty m ents], fun _ Hin => List.mem_singleton.1 Hin, ?_⟩, rfl,
      stepdown_frame (by rw [Hty]; w32_ne) (Int.le_of_lt Hgt) rfl rfl rfl rfl rfl⟩
    refine StepCD.frame ?_ (by rframe)
    rw [toPState_prvals_nl (becomeFollower s m.Term' (W64 0)) pvs
      (by simp [becomeFollower]), toPState_becomeFollower]
    have Hst := StepCF.higherTerm (c := c) (id := id) (absMsg ty m ents) (toPState s) Hgt Hto
      (fun h => by simp [absMsg, absMsgFrom, Hfl] at h)
    rw [show (if fromLeader (absMsg ty m ents).ty then (absMsg ty m ents).src else W64 0)
      = W64 0 by simp [absMsg, absMsgFrom, Hfl]] at Hst
    exact Hst

end StepProof

end branches

end EtcdGrove
end Perennial
