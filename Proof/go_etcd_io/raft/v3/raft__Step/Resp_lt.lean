/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_Resp_lt.v.

The lower-term case of `Step`'s `MsgAppResp` and `MsgHeartbeatResp` branches, for both
types at once, in its own file so that it checks in parallel with the other term cases
-- see `MsgAppResp.lean` and `MsgHeartbeatResp.lean`, which combine them. Proof
structure, not specification: no `Module Type`, no `Parameter`; only files in this
directory may import it.

Lean notes:
* The branch lemma takes the callee specs (Rocq's functor argument
  `P : STEP_POSTULATES`) as its first argument `_P : raft.Step.Postulates`, and Rocq's
  section variable `c` as its second.
* Rocq's `Local Ltac` `ne_ty` is not ported
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

namespace StepProof

set_option maxHeartbeats 1000000 in
/-- `m.Term < r.Term` for a `MsgAppResp` or `MsgHeartbeatResp`: with `checkQuorum` and
`preVote` both off, and the type neither `MsgPreVote` nor `MsgStorageAppendResp`, the
stale message is only logged, then `return nil`. `StepC.refl`, nothing received. -/
theorem wp_Step_Resp_lt (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (_Q : raft.Step.ReplPbPostulates (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc)
    (ents : List EntryM) (ty : MsgType) :
    m.Type' = MsgAppResp ∨ m.Type' = MsgHeartbeatResp →
    m.Term' ≠ W64 0 →
    uint.Z m.Term' < uint.Z s.term →
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
        "%Hresp" ∷ ⌜RespStep m s s'⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ }} := by
  intro Hty Hterm Hlt Hwf
  wp_start as H
  iNamed H
  icases msgPtsC_nn _ _ _ _ _ $$ Hm with ⟨%Hnn, Hm⟩
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply _P.traceReceiveMessage
  try wp_auto
  wp_get _Q
  rw [decide_eq_false Hterm]
  wp_auto
  wp_drive _Q
  rw [decide_eq_false (show ¬ (uint.Z s.term < uint.Z m.Term') by omega)]
  wp_auto
  wp_drive _Q
  rw [decide_eq_true Hlt]
  wp_auto
  -- (2026-10-17) `(checkQuorum || preVote) && (MsgHeartbeat || MsgApp)`: `checkQuorum`, then
  -- (off) the pre-vote flag (`cq_split`); the type test is false either way, so the test is
  -- joined (`wp_join`) at `#false` and the rest verified once per type
  rcases Hty with Hty | Hty
  all_goals
    wp_join (v := #false) at (if: _ then _ else #false) with [Hphys r m Hm]
    · wp_drive _Q
      cq_split _Q
      -- at the join value (`#false`, or the closed `decide` of the last type test)
      all_goals
        isplitr
        · ipureintro; first | trivial | rfl
        iframe
    wp_drive _Q
    wp_raft_logC
    iapply HΦ $$ %interface.nil %s
    iframe Hphys
    ipureintro
    exact ⟨Hwf, ⟨[], fun _ Hin => absurd Hin List.not_mem_nil, StepCD.frame (.refl _) (RFrame.refl _)⟩, rfl,
      RespStep.refl _ _, keep_frame rfl rfl rfl rfl rfl⟩

end StepProof

end branches

end EtcdGrove
end Perennial
