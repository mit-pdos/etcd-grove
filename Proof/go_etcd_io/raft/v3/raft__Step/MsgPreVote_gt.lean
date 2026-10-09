/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgPreVote_gt.v.

One term case of `Step`'s `MsgPreVote` branch (2026-10-04): the incoming term is
higher. In its own file so that it checks in parallel with the others;
`MsgPreVote.lean` combines them. Proof structure, not specification: no `Module Type`,
no `Parameter`; only files in this directory may import it.

Lean notes:
* The branch lemma takes the callee specs (Rocq's functor argument
  `P : STEP_POSTULATES`) as its first argument `_P : raft.Step.Postulates`, and Rocq's
  section variable `cfg` as its second.
* Rocq's `Local Ltac cv_step` (one step of `canVote`'s evaluation: a field load
  through `raft.wp_load_Vote`/`wp_load_lead`/`wp_load_Term`, or a `bool_decide`
  decided by case analysis) is the local macro `cv_step` (with `wp_if_destruct` for
  the case analysis); `canVote`'s evaluation is joined with `wp_join` (Rocq:
  `wp_bind` + `wp_wand`). The answer's tail, written out three times in Rocq, is the
  local macro `prevote_resp_tail`.
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
/-- Rocq `cv_step`: one step of `canVote`'s evaluation, whatever its outcome: a field
load, or a comparison decided by case analysis. Works on `Hphys`. -/
local macro "cv_step" : tactic =>
  `(tactic| first
    | wp_auto
    | wp_apply Perennial.EtcdGrove.raft.wp_load_Vote $$ Hphys as Hphys
    | wp_apply Perennial.EtcdGrove.raft.wp_load_lead $$ Hphys as Hphys
    | wp_apply Perennial.EtcdGrove.raft.wp_load_Term $$ Hphys as Hphys
    | wp_if_destruct)

set_option hygiene false in
/-- The answer's tail, granted or rejected: the log call, `voteRespMsgType`, `send`, and
(after a grant) the `MsgVote` test, then `Step.sendFree`. Uses `Hphys`, `HΦ`, `Hty`,
`Hwf`, and the answer's term being nonzero as `Hterm` (a grant at `m.Term`) or `Hs0`
(a rejection at `r.Term`). -/
local macro "prevote_resp_tail" : tactic =>
  `(tactic| (
    wp_apply Perennial.EtcdGrove.raft.wp_load_id $$ Hphys as Hphys
    wp_apply Perennial.EtcdGrove.raft.wp_load_Vote $$ Hphys as Hphys
    wp_apply Perennial.EtcdGrove.raft.wp_load_Term $$ Hphys as Hphys
    wp_raft_log
    try (wp_apply Perennial.EtcdGrove.raft.wp_load_Term $$ Hphys as Hphys)
    wp_apply _P.voteRespMsgType m.Type' _ (.inr ⟨Hty, rfl⟩)
    wp_apply _P.send cfg r id s _ [] _ (Or.inl rfl)
        (Or.inl ⟨.preVoteResp, Or.inr (Or.inr (Or.inr rfl)), mtypeOf_MsgPreVoteResp,
          by first | exact Hterm | exact Hs0,
          fun Hc => by rcases Hc with Hc | Hc <;> exact absurd Hc (by w32_ne), rfl⟩)
      $$ [Hphys]
    · iframe Hphys
      isplitr
      · iapply ownSlice_nil
      iapply send_no_snap
      w32_ne
    iintro Hphys
    wp_auto
    -- not a `MsgVote`: no vote recorded
    try (rw [decide_eq_false (show m.Type' ≠ W32 5 by rw [Hty]; w32_ne)]; wp_auto)
    iapply HΦ $$ %interface.nil %_
    iframe Hphys
    ipureintro
    refine ⟨nstateWf_sendMsgs _ _ Hwf, ?_, rfl, keep_frame rfl rfl rfl rfl rfl⟩
    rw [toPState_sendMsgs]
    exact .sendFree _ _ (.inr rfl) rfl))

/-- `MsgPreVote` with `m.Term > r.Term`: the lease check passes (`checkQuorum` is off),
and a pre-vote **never** steps the node down. `canVote` holds by its third disjunct
(`MsgPreVote` for a future term). The answer is a `MsgPreVoteResp`: granted at `m.Term`
if the candidate's log is up to date, else rejected at `r.Term`; nothing is recorded
either way. Both are free messages: `Step.sendFree`. The rejection's `Term` is the
node's own, which `send` needs non-zero: at term `0` the candidate is up to date (the
premise `Hutd0`). -/
theorem wp_Step_MsgPreVote_gt (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message) :
    m.Type' = MsgPreVote →
    m.To' = id →
    m.Term' ≠ W64 0 →
    m.From' ≠ W64 0 →
    -- this file: the incoming term is strictly higher
    uint.Z s.term < uint.Z m.Term' →
    NStateWf s →
    (s.term = W64 0 →
      plogUpToDate s.logst.prev (s.logst.sents ++ s.logst.uents)
        (entryID.mk m.LogTerm' m.Index') = true) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhys cfg r id s ∗
        "#Hctx" ∷ (∃ (ctx : List w8), m.Context' ↦*□ ctx ∗ ⌜ctx ≠ campaignTransfer⌝) }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhys cfg r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜Step cfg id (toPState s) [] (toPState s')⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ }} := by
  intro Hty Hto Hterm Hfnz Hgt0 Hwf Hutd0
  have Hn5 : decide (m.Type' = W32 5) = false := decide_eq_false (by rw [Hty]; w32_ne)
  have Hy17 : decide (m.Type' = W32 17) = true := decide_eq_true Hty
  wp_start as ⟨Hphys, #Hctx⟩
  wp_auto
  wp_apply _P.traceReceiveMessage
  -- `m.Term ≠ 0`, so the first arm of the term preamble is skipped
  rw [decide_eq_false Hterm]
  wp_auto
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  rw [decide_eq_true Hgt0]
  wp_auto
  -- `MsgVote || MsgPreVote`: the lease check
  try (rw [Hn5]; wp_auto)
  rw [Hy17]
  wp_auto
  -- `force` is false (not a leader transfer) and `inLease` is false (no check-quorum),
  -- so the lease check does not drop the message
  icases Hctx with ⟨%ctx, Hctx_sl, %Hctx_ne⟩
  wp_apply wp_string_to_bytes as %ct_sl ⟨ct_sl, -⟩
  wp_apply bytes.wp_Equal _ _ DFrac.discard (DFrac.own 1) ctx (go!"CampaignTransfer")
      $$ [$Hctx_sl $ct_sl] as ⟨-, -⟩
  wp_apply raft.wp_load_checkQuorum $$ Hphys as Hphys
  have Hctx_ne' : ctx ≠ go!"CampaignTransfer" := Hctx_ne
  rw [decide_eq_false Hctx_ne']
  try wp_auto
  -- the step-down switch: `MsgPreVote`, so nothing
  rw [Hy17]
  wp_auto
  -- the type switch: not `MsgHup` / `MsgStorageAppendResp` / `MsgStorageApplyResp`,
  -- but `MsgPreVote`
  rw [Hty]
  wp_auto
  -- `canVote`: true by its third disjunct, whichever way the first two go; the
  -- evaluation is joined
  wp_join (Q := fun v => iprop(⌜v = #true⌝ ∗ ownRaftPhys cfg r id s ∗
      r_ptr ↦ r ∗ m_ptr ↦ m)) at (if: _ then _ else _) with [Hphys r m]
    as ⟨%Hv, Hphys, r, m⟩
  · repeat (any_goals cv_step)
    all_goals first | wp_join_done | (exfalso; omega) | (exfalso; exact Hif Hty)
  subst Hv
  wp_auto
  -- `lastEntryID`, then `isUpToDate`
  wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
  icases ownRaftPhys_log_same cfg r id _ $$ Hphys with ⟨Hlog, Hback⟩
  wp_apply _P.lastEntryID $$ [$Hlog] as %lastID ⟨Hlog, -⟩
  ihave Hphys := Hback $$ Hlog
  wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
  icases ownRaftPhys_log_same cfg r id _ $$ Hphys with ⟨Hlog, Hback⟩
  wp_apply _P.isUpToDate $$ [$Hlog] as %uptodate ⟨Hlog, %Hutd⟩
  ihave Hphys := Hback $$ Hlog
  cases uptodate
  · -- behind: reject at `r.Term`, which is not `0`
    have Hs0 : s.term ≠ W64 0 := fun H0 => by
      have := Hutd0 H0
      rw [← Hutd] at this
      exact Bool.false_ne_true this
    wp_auto
    prevote_resp_tail
  -- up to date: grant at `m.Term`, recording nothing
  wp_auto
  prevote_resp_tail

end StepProof

end branches

end EtcdGrove
end Perennial
