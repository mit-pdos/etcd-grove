/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgPreVoteResp_eq.v.

One term case of `Step`'s `MsgPreVoteResp` branch (2026-10-04): the incoming term is
the node's own. In its own file so that it checks in parallel with the others;
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

public import RaftWitness.Proof.go_etcd_io.raft.v3.raft__Step.prevote_lemmas
public import RaftWitness.Proof.go_etcd_io.raft.v3.raft__Step.ElectionLemmas

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
/-- `MsgPreVoteResp` at `m.Term = r.Term`: the preamble does nothing and the type
switch's default arm runs `r.step(m)`. Only a pre-candidate acts on it (`stepCandidate`
with `myVoteRespType = MsgPreVoteResp`: the tally, then `campaign(campaignElection)` on
a win, `becomeFollower` on a loss); everyone else ignores it. Nothing is received by
the protocol: `StepC.refl`, `StepC.abandon` or `StepC.campaign`
(`stepC_prevoteRespResult`). -/
theorem wp_Step_MsgPreVoteResp_eq (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (PB : raft.Step.PbPostulates (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc) :
    m.Type' = MsgPreVoteResp →
    m.To' = id →
    m.Term' ≠ W64 0 →
    -- this file: the same term
    m.Term' = s.term →
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
  intro Hty Hto Hterm Hteq Hnw Hwf
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
  rw [decide_eq_false (show ¬ uint.Z s.term < uint.Z m.Term' by rw [Hteq]; omega)]
  try wp_auto
  wp_gets
  wp_apply raft.wp_load_TermC $$ Hphys as Hphys
  wp_gets
  rw [decide_eq_false (show ¬ uint.Z m.Term' < uint.Z s.term by rw [Hteq]; omega)]
  try wp_auto
  -- the type switch: none of its four cases, so `r.step(m)`
  wp_gets
  rw [Hty]
  try wp_auto
  prevote_resp_dispatch

end StepProof

end branches

end EtcdGrove
end Perennial
