/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgPreVote_eq.v.

One term case of `Step`'s `MsgPreVote` branch (2026-10-04): the incoming term is the
node's own. In its own file so that it checks in parallel with the others;
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
test is true (`Hty`), then the term comparison, whatever its outcome. -/
local macro "cv_third" : tactic =>
  `(tactic| (
    wp_load; wp_pures
    wp_if_destruct
    · wp_load; wp_load; wp_pures
      wp_apply Perennial.EtcdGrove.raft.wp_load_Term $$ Hphys as Hphys
      wp_pures
      iframe; ipureintro; exact ⟨_, rfl⟩
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

/-- `MsgPreVote` with `m.Term = r.Term`: the preamble does nothing, and the vote arm
answers with a `MsgPreVoteResp` -- granted at `m.Term` or rejected at `r.Term`, the same
term -- recording nothing. What `canVote` evaluates to does not matter to the protocol:
either answer is a free message (`Step.sendFree`). -/
theorem wp_Step_MsgPreVote_eq (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message) :
    m.Type' = MsgPreVote →
    m.To' = id →
    m.Term' ≠ W64 0 →
    m.From' ≠ W64 0 →
    -- this file: the same term
    m.Term' = s.term →
    NStateWf s →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhys cfg r id s }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhys cfg r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜Step cfg id (toPState s) [] (toPState s')⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ }} := by
  intro Hty Hto Hterm Hfnz Heq0 Hwf
  have Hs0 : s.term ≠ W64 0 := Heq0 ▸ Hterm
  wp_start as Hphys
  iNamed Hphys
  wp_alloc r_ptr as r; wp_pures; wp_alloc m_ptr as m; wp_pures; wp_load; wp_pures
  wp_apply _P.traceReceiveMessage
  wp_pures; wp_load; wp_pures
  -- `m.Term ≠ 0`, so the first arm of the term preamble is skipped
  rw [decide_eq_false Hterm]
  wp_pures; wp_load; wp_load; wp_pures
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  wp_pures
  rw [decide_eq_false (show ¬ uint.Z s.term < uint.Z m.Term' by rw [Heq0]; omega)]
  wp_pures; wp_load; wp_load; wp_pures
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  wp_pures
  rw [decide_eq_false (show ¬ uint.Z m.Term' < uint.Z s.term by rw [Heq0]; omega)]
  wp_pures; wp_load; wp_pures
  -- the type switch: not `MsgHup` / `MsgStorageAppendResp` / `MsgStorageApplyResp`,
  -- but `MsgPreVote`
  rw [Hty]
  wp_pures; wp_load; wp_pures
  -- `canVote`, whatever it is; the evaluation is joined
  wp_join (Q := fun v => iprop(⌜∃ b : Bool, v = #b⌝ ∗ ownRaftPhys cfg r id s ∗
      r_ptr ↦ r ∗ m_ptr ↦ m)) at (if: _ then _ else _) with [Hphys r m]
    as ⟨%Hv, Hphys, r, m⟩
  · -- `r.Vote == m.From`
    wp_apply raft.wp_load_Vote $$ Hphys as Hphys
    wp_pures; wp_load; wp_pures
    wp_if_destruct
    · iframe; ipureintro; exact ⟨_, rfl⟩
    -- `r.Vote == None && r.lead == None`
    wp_load; wp_pures
    wp_apply raft.wp_load_Vote $$ Hphys as Hphys
    wp_pures
    wp_if_destruct
    · wp_load; wp_pures
      wp_apply raft.wp_load_lead $$ Hphys as Hphys
      wp_pures
      wp_if_destruct
      · iframe; ipureintro; exact ⟨_, rfl⟩
      cv_third
    cv_third
  obtain ⟨cv, rfl⟩ := Hv
  wp_pures; wp_alloc canVote_ptr as canVote; wp_pures
  wp_store; wp_pures; wp_load; wp_pures
  wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
  wp_pures
  icases ownRaftPhys_log_same cfg r id _ $$ Hphys with ⟨Hlog, Hback⟩
  wp_apply _P.lastEntryID $$ [$Hlog] as %lastID ⟨Hlog, -⟩
  wp_pures; wp_alloc lastID_ptr as lastID; wp_pures; wp_store; wp_pures; wp_load; wp_pures; wp_load
  wp_pures; wp_alloc candLastID_ptr as candLastID; wp_pures; wp_store; wp_pures; wp_load
  iclear canVote
  ihave Hphys := Hback $$ Hlog
  -- `canVote && isUpToDate(…)`: the reject arm is reached two ways
  cases cv
  · -- cannot vote: reject at `r.Term`
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
  wp_pures; wp_load; wp_pures; wp_load; wp_pures
  wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
  wp_pures
  icases ownRaftPhys_log_same cfg r id _ $$ Hphys with ⟨Hlog, Hback⟩
  wp_apply _P.isUpToDate $$ [$Hlog] as %uptodate ⟨Hlog, -⟩
  ihave Hphys := Hback $$ Hlog
  cases uptodate
  · -- behind: reject
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
  -- grant at `m.Term`, recording nothing
  wp_pures; wp_load; wp_pures
  prevote_resp_log
  wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures
  wp_apply _P.voteRespMsgType m.Type' _ (.inr ⟨Hty, rfl⟩)
  wp_pures; wp_load; wp_pures
  prevote_resp_send
  wp_pures; wp_load; wp_pures
  -- not a `MsgVote`: no vote recorded
  rw [decide_eq_false (show m.Type' ≠ W32 5 by rw [Hty]; w32_ne)]
  wp_pures
  prevote_resp_done

end StepProof

end branches

end EtcdGrove
end Perennial
