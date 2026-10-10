/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgPreVote_eq.v.

One term case of `Step`'s `MsgPreVote` branch (2026-10-04): the incoming term is the
node's own. In its own file so that it checks in parallel with the others;
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
          fun Hc => by rcases Hc with Hc | Hc <;> exact absurd Hc (by w32_ne),
          fun h => absurd h Hfid, rfl⟩)
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
    -- from another node (2026-10-10): the answer goes to `m.From`
    m.From' ≠ id →
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
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ }} := by
  intro Hty Hto Hterm Hfnz Hfid Heq0 Hwf
  have Hs0 : s.term ≠ W64 0 := Heq0 ▸ Hterm
  wp_start as Hphys
  iNamed Hphys
  wp_auto
  wp_apply _P.traceReceiveMessage
  -- `m.Term ≠ 0`, so the first arm of the term preamble is skipped
  rw [decide_eq_false Hterm]
  wp_auto
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  rw [decide_eq_false (show ¬ uint.Z s.term < uint.Z m.Term' by rw [Heq0]; omega)]
  wp_auto
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  rw [decide_eq_false (show ¬ uint.Z m.Term' < uint.Z s.term by rw [Heq0]; omega)]
  wp_auto
  -- the type switch: not `MsgHup` / `MsgStorageAppendResp` / `MsgStorageApplyResp`,
  -- but `MsgPreVote`
  rw [Hty]
  wp_auto
  -- `canVote`, whatever it is; the evaluation is joined
  wp_join (Q := fun v => iprop(⌜∃ b : Bool, v = #b⌝ ∗ ownRaftPhys cfg r id s ∗
      r_ptr ↦ r ∗ m_ptr ↦ m)) at (if: _ then _ else _) with [Hphys r m]
    as ⟨%Hv, Hphys, r, m⟩
  · repeat (any_goals cv_step)
    all_goals (iframe; ipureintro; exact ⟨_, rfl⟩)
  obtain ⟨cv, rfl⟩ := Hv
  wp_auto
  wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
  icases ownRaftPhys_log_same cfg r id _ $$ Hphys with ⟨Hlog, Hback⟩
  wp_apply _P.lastEntryID $$ [$Hlog] as %lastID ⟨Hlog, -⟩
  ihave Hphys := Hback $$ Hlog
  -- `canVote && isUpToDate(…)`: the reject arm is reached two ways
  cases cv
  · -- cannot vote: reject at `r.Term`
    wp_auto
    prevote_resp_tail
  wp_auto
  wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
  icases ownRaftPhys_log_same cfg r id _ $$ Hphys with ⟨Hlog, Hback⟩
  wp_apply _P.isUpToDate $$ [$Hlog] as %uptodate ⟨Hlog, -⟩
  ihave Hphys := Hback $$ Hlog
  cases uptodate
  · -- behind: reject
    wp_auto
    prevote_resp_tail
  -- grant at `m.Term`, recording nothing
  wp_auto
  prevote_resp_tail

end StepProof

end branches

end EtcdGrove
end Perennial
