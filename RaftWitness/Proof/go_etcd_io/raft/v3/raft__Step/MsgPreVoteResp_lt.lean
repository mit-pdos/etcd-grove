/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgPreVoteResp_lt.v.

One term case of `Step`'s `MsgPreVoteResp` branch (2026-10-04): the incoming term is
stale. In its own file so that it checks in parallel with the others;
`MsgPreVoteResp.lean` combines them. Proof structure, not specification: no
`Module Type`, no `Parameter`; only files in this directory may import it.

Lean notes:
* The branch lemma takes the callee specs (Rocq's functor argument
  `P : STEP_POSTULATES`) as its first argument `_P : raft.Step.Postulates`, and Rocq's
  section variable `c` as its second.
* Rocq's `Local Ltac ne_ty` (`bool_decide (m.Type = c) = false` by `w32_ne`) is not
  ported.

raft v3.7 (2026-10-15, stage R4 phase 3): the message is a pointer `ml` with `msgIn ml □ ⟨m, ents,
sn, ctx, rs⟩`, read by its getters (`wp_get`/`wp_gets`, `ElectionLemmas.lean`, by `PB`); `Step`
first checks `m != nil` (`msgPtsC_nn`).
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
/-- `MsgPreVoteResp` with `m.Term < r.Term`: logged and dropped. `StepC.refl`, nothing
received. -/
theorem wp_Step_MsgPreVoteResp_lt (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (PB : raft.Step.PbPostulates (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc) :
    m.Type' = MsgPreVoteResp →
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
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absMsg .preVoteResp m ents) ∧
            StepCD c id B m s recv s'⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hresp" ∷ ⌜RespStep m s s'⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ }} := by
  intro Hty Hterm Hlt Hwf
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
  rw [decide_eq_false Hterm]
  try wp_auto
  wp_gets
  wp_apply raft.wp_load_TermC $$ Hphys as Hphys
  wp_gets
  rw [decide_eq_false (show ¬ uint.Z s.term < uint.Z m.Term' by omega)]
  try wp_auto
  wp_gets
  wp_apply raft.wp_load_TermC $$ Hphys as Hphys
  wp_gets
  rw [decide_eq_true Hlt]
  try wp_auto
  wp_gets
  have Hn8 : decide (m.Type' = W32 8) = false := decide_eq_false (by rw [Hty]; w32_ne)
  have Hn3 : decide (m.Type' = W32 3) = false := decide_eq_false (by rw [Hty]; w32_ne)
  have Hn17 : decide (m.Type' = W32 17) = false := decide_eq_false (by rw [Hty]; w32_ne)
  have Hn20 : decide (m.Type' = W32 20) = false := decide_eq_false (by rw [Hty]; w32_ne)
  wp_cq_pv
  -- with `checkQuorum` or pre-vote on the type test runs and is false
  all_goals try (wp_gets; rw [Hn8]; try wp_auto; wp_gets; rw [Hn3]; try wp_auto)
  all_goals
    wp_gets
    rw [Hn17]
    try wp_auto
    wp_gets
    rw [Hn20]
    try wp_auto
    wp_gets
    wp_apply raft.wp_load_idC $$ Hphys as Hphys
    wp_gets
    wp_apply raft.wp_load_TermC $$ Hphys as Hphys
    wp_gets
    wp_raft_logC
    iapply HΦ $$ %interface.nil %s
    iframe Hphys
    ipureintro
    exact ⟨Hwf, ⟨[], fun _ h => absurd h List.not_mem_nil, StepCD.frame (.refl _) (RFrame.refl _)⟩, rfl,
      RespStep.refl _ _, keep_frame rfl rfl rfl rfl rfl⟩

end StepProof

end branches

end EtcdGrove
end Perennial
