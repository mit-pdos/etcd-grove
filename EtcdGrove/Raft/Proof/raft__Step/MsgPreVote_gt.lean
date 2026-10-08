/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgPreVote_gt.v.

One term case of `Step`'s `MsgPreVote` branch (2026-10-04): the incoming term is
higher. In its own file so that it checks in parallel with the others;
`MsgPreVote.lean` combines them. Proof structure, not specification: no `Module Type`,
no `Parameter`; only files in this directory may import it.

Lean notes:
* The branch lemma takes the callee specs (Rocq's functor argument
  `P : STEP_POSTULATES`) as its first argument `_P : raft.Step.Postulates`, and Rocq's
  section variable `cfg` as its second.
* Rocq's `Local Ltac cv_step` (one step of `canVote`'s evaluation, repeated) is
  replaced by `canVote`'s evaluation written out: each disjunct's loads and its
  `wp_if_destruct`, the third disjunct (`MsgPreVote && m.Term > r.Term`, reached from
  two arms) as the local macro `cv_third`. The evaluation is joined with `wp_join`
  (Rocq: `wp_bind` + `wp_wand`). The answer's tail, written out three times in Rocq,
  is the local macros `prevote_resp_log`, `prevote_resp_send` and `prevote_resp_done`,
  with the steps that differ between a grant and a rejection at the call sites.
-/
import EtcdGrove.Raft.Proof.raft__Step.prevote_lemmas

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

set_option hygiene false in
/-- `canVote`'s third disjunct, `m.Type == MsgPreVote && m.Term > r.Term`: the type
test is true (`Hty`), then the term comparison. -/
local macro "cv_third" : tactic =>
  `(tactic| (
    wp_load; wp_pures
    wp_if_destruct
    · wp_load; wp_load; wp_pures
      wp_apply Perennial.EtcdGrove.raft.wp_load_Term $$ Hphys as Hphys
      wp_pures
      rw [decide_eq_true Hgt0]
      wp_join_done
    · exfalso; exact Hif Hty))

set_option hygiene false in
/-- The answer's log line, granted or rejected (right after `isUpToDate`'s result is
stored). Works on `Hphys`. The steps after `logf` differ between the two answers and
are at the call sites. -/
local macro "prevote_resp_log" : tactic =>
  `(tactic| (
    wp_apply Perennial.EtcdGrove.raft.wp_load_id $$ Hphys as Hphys
    wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures; iclear lastID
    wp_apply Perennial.EtcdGrove.raft.wp_load_Vote $$ Hphys as Hphys
    wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures
    wp_load; wp_pures; iclear candLastID
    wp_apply Perennial.EtcdGrove.raft.wp_load_Term $$ Hphys as Hphys
    wp_pures
    wp_raft_log))

set_option hygiene false in
/-- The answer's `send`. Uses `Hphys`, `Hty`, and the answer's term being nonzero as
`Hterm` (a grant at `m.Term`) or `Hs0` (a rejection at `r.Term`). -/
local macro "prevote_resp_send" : tactic =>
  `(tactic| (
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
    iintro Hphys))

set_option hygiene false in
/-- The postcondition after the answer is sent: `Step.sendFree`. Uses `Hphys`, `HΦ`,
`Hwf`. -/
local macro "prevote_resp_done" : tactic =>
  `(tactic| (
    iapply HΦ $$ %interface.nil %_
    iframe Hphys
    ipureintro
    refine ⟨nstateWf_sendMsgs _ _ Hwf, ?_, rfl⟩
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
        "%Herr" ∷ ⌜err = interface.nil⌝ }} := by
  intro Hty Hto Hterm Hfnz Hgt0 Hwf Hutd0
  have Hn5 : decide (m.Type' = W32 5) = false := decide_eq_false (by rw [Hty]; w32_ne)
  have Hy17 : decide (m.Type' = W32 17) = true := decide_eq_true Hty
  wp_start as ⟨Hphys, #Hctx⟩
  wp_alloc r_ptr as r; wp_pures; wp_alloc m_ptr as m; wp_pures; wp_load; wp_pures
  wp_apply _P.traceReceiveMessage
  wp_pures; wp_load; wp_pures
  -- `m.Term ≠ 0`, so the first arm of the term preamble is skipped
  rw [decide_eq_false Hterm]
  wp_pures; wp_load; wp_load; wp_pures
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  wp_pures
  rw [decide_eq_true Hgt0]
  wp_pures; wp_load; wp_pures
  -- `MsgVote || MsgPreVote`: the lease check
  try (rw [Hn5]; (wp_pures; wp_load; wp_pures))
  rw [Hy17]
  wp_pures; wp_load; wp_pures
  -- `force` is false (not a leader transfer) and `inLease` is false (no check-quorum),
  -- so the lease check does not drop the message
  icases Hctx with ⟨%ctx, Hctx_sl, %Hctx_ne⟩
  wp_apply wp_string_to_bytes as %ct_sl ⟨ct_sl, -⟩
  wp_pures
  wp_apply bytes.wp_Equal _ _ DFrac.discard (DFrac.own 1) ctx (go!"CampaignTransfer")
      $$ [$Hctx_sl $ct_sl] as ⟨-, -⟩
  wp_pures; wp_alloc force_ptr as force; wp_pures; wp_store; wp_pures; wp_load; wp_pures
  wp_apply raft.wp_load_checkQuorum $$ Hphys as Hphys
  wp_pures; wp_alloc inLease_ptr as inLease; wp_pures; wp_store; wp_pures; wp_load; wp_pures
  iclear force
  have Hctx_ne' : ctx ≠ go!"CampaignTransfer" := Hctx_ne
  rw [decide_eq_false Hctx_ne']
  wp_pures; wp_load; wp_pures; wp_load; wp_pures; iclear inLease
  -- the step-down switch: `MsgPreVote`, so nothing
  rw [Hy17]
  wp_pures; wp_load; wp_pures
  -- the type switch: not `MsgHup` / `MsgStorageAppendResp` / `MsgStorageApplyResp`,
  -- but `MsgPreVote`
  rw [Hty]
  wp_pures; wp_load; wp_pures
  -- `canVote`: true by its third disjunct, whichever way the first two go; the
  -- evaluation is joined
  wp_join (Q := fun v => iprop(⌜v = #true⌝ ∗ ownRaftPhys cfg r id s ∗
      r_ptr ↦ r ∗ m_ptr ↦ m)) at (if: _ then _ else _) with [Hphys r m]
    as ⟨%Hv, Hphys, r, m⟩
  · -- `r.Vote == m.From`
    wp_apply raft.wp_load_Vote $$ Hphys as Hphys
    wp_pures; wp_load; wp_pures
    wp_if_destruct
    · wp_join_done
    -- `r.Vote == None && r.lead == None`
    wp_load; wp_pures
    wp_apply raft.wp_load_Vote $$ Hphys as Hphys
    wp_pures
    wp_if_destruct
    · wp_load; wp_pures
      wp_apply raft.wp_load_lead $$ Hphys as Hphys
      wp_pures
      wp_if_destruct
      · wp_join_done
      cv_third
    cv_third
  subst Hv
  wp_pures; wp_alloc canVote_ptr as canVote; wp_pures
  wp_store; wp_pures; wp_load; wp_pures
  -- `lastEntryID`, then `isUpToDate`
  wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
  wp_pures
  icases ownRaftPhys_log_same cfg r id _ $$ Hphys with ⟨Hlog, Hback⟩
  wp_apply _P.lastEntryID $$ [$Hlog] as %lastID ⟨Hlog, -⟩
  wp_pures; wp_alloc lastID_ptr as lastID; wp_pures; wp_store; wp_pures; wp_load; wp_pures; wp_load
  wp_pures; wp_alloc candLastID_ptr as candLastID; wp_pures; wp_store; wp_pures; wp_load; wp_pures
  wp_load; wp_pures; wp_load; wp_pures; iclear canVote
  ihave Hphys := Hback $$ Hlog
  wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
  wp_pures
  icases ownRaftPhys_log_same cfg r id _ $$ Hphys with ⟨Hlog, Hback⟩
  wp_apply _P.isUpToDate $$ [$Hlog] as %uptodate ⟨Hlog, %Hutd⟩
  ihave Hphys := Hback $$ Hlog
  cases uptodate
  · -- behind: reject at `r.Term`, which is not `0`
    have Hs0 : s.term ≠ W64 0 := fun H0 => by
      have := Hutd0 H0
      rw [← Hutd] at this
      exact Bool.false_ne_true this
    wp_pures; wp_load; wp_pures
    prevote_resp_log
    wp_pures; wp_load; wp_pures; wp_load; wp_pures
    -- `Term: r.Term` and the `voteRespMsgType` call
    wp_apply raft.wp_load_Term $$ Hphys as Hphys
    wp_pures; wp_load; wp_pures; iclear m
    wp_apply _P.voteRespMsgType m.Type' _ (.inr ⟨Hty, rfl⟩)
    wp_pures; wp_load; wp_pures; iclear r
    prevote_resp_send
    wp_pures
    prevote_resp_done
  -- up to date: grant at `m.Term`, recording nothing
  wp_pures; wp_load; wp_pures
  prevote_resp_log
  wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures
  wp_apply _P.voteRespMsgType m.Type' _ (.inr ⟨Hty, rfl⟩)
  wp_pures; wp_load; wp_pures
  prevote_resp_send
  wp_pures; wp_load; wp_pures
  -- not a `MsgVote`: no vote recorded
  rw [Hn5]
  wp_pures
  prevote_resp_done

end StepProof

end branches

end EtcdGrove
end Perennial
