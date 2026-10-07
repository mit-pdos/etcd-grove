/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgVote_gt.v.

One term case of `Step`'s `MsgVote` branch, in its own file so that it checks in
parallel with the other -- see `proof_raft__Step_MsgVote.v` (`MsgVote.lean`), which
combines the two, and `notes/decisions.md` (2026-09-17; 2026-09-18 for why this
directory exists). Proof structure, not specification: no `Module Type`, no
`Parameter`; only `MsgVote.lean` may import this module.

Lean notes:
* The branch lemma takes the callee specs (Rocq's functor argument `P : STEP_POSTULATES`)
  as its first argument `_P : raft.Step.Postulates`, and Rocq's section variable `cfg`
  as its second.
* Rocq's `Local Ltac recv_elem` (`∀ m' ∈ recv, m' = a` for the concrete `recv` lists
  `[]`, `[a]`, `[a] ++ [a]`, by rewriting the membership away rather than `set_solver`,
  which took 150s and more there) is not ported.
* The type tests `m.Type' = W32 k` (all false: `m` is a `MsgVote`) are the local macro
  `ty_ne k`.
* After `becomeFollower`, the state `{ becomeFollower s m.Term' (W64 0) with prvals :=
  pvs }` is named `s1` (`ownRaftPhys_eq`), with its `vote`/`lead`/`term` and its
  `toPState` (`Hps1`) as separate facts: the loads then return `s1.vote` etc., which a
  `rw` can rewrite (on the unnamed record the `decide`'s instance blocks the rewrite).
  The two outcomes end in `step_stepdown_then_vote` / `step_stepdown_then_reject`
  (`StepLemmas.lean`) rather than `Step.trans` of the step-down and the answer.
-/
import EtcdGrove.Raft.Proof.raft__Step.Base

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
/-- `m.Type' = W32 k` is false: `m` is a `MsgVote` (`Hty`). -/
local macro "ty_ne " k:num : tactic =>
  `(tactic| rw [decide_eq_false (show m.Type' ≠ W32 $k by rw [Hty]; w32_ne)])

/-- `MsgVote` with `m.Term > r.Term`: step down to follower first, then grant or decline
in the new term. -/
theorem wp_Step_MsgVote_gt (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) :
    m.Type' = MsgVote →
    m.To' = id →
    m.Term' ≠ W64 0 →
    -- `send` stamps the sender's id into `From`, and node ids are nonzero
    m.From' ≠ W64 0 →
    -- this file: the incoming term is strictly higher, so `Step` steps down first
    uint.Z s.term < uint.Z m.Term' →
    -- `r.step` matches the role
    NStateWf s →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhys cfg r id s ∗
        -- the message's `Context` is readable and is not the leader-transfer marker:
        -- leader transfer is out of scope
        "#Hctx" ∷ (∃ (ctx : List w8), m.Context' ↦*□ ctx ∗ ⌜ctx ≠ campaignTransfer⌝) }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhys cfg r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        -- `recv` is whatever this branch consumed -- nothing, or the incoming message
        -- once or twice. Naming its elements rather than the list lets
        -- `raft.Step.wp_proof` discharge the `isMessage` side of `ownRaftGhost_step`
        -- from the single fact it holds about `m`.
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absMsg .vote m ents) ∧
            Step cfg id (toPState s) recv (toPState s')⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ }} := by
  intro Hty Hto Hterm Hfnz Hgt0 Hwf
  wp_start as ⟨Hphys, #Hctx⟩
  wp_auto
  wp_apply _P.traceReceiveMessage
  -- `m.Term ≠ 0`, so the first arm of the term preamble is skipped
  rw [decide_eq_false Hterm]
  wp_auto
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  rw [decide_eq_true Hgt0]
  wp_auto
  rw [Hty]
  wp_auto
  -- `force` is false (not a leader transfer) and `inLease` is false (no check-quorum),
  -- so the lease check does not drop the message
  icases Hctx with ⟨%ctx, Hctx_sl, %Hctx_ne⟩
  wp_apply wp_string_to_bytes as %ct_sl ⟨ct_sl, -⟩
  wp_apply bytes.wp_Equal _ _ DFrac.discard (DFrac.own 1) ctx (go!"CampaignTransfer") $$ [$Hctx_sl $ct_sl]
    as ⟨-, -⟩
  wp_apply raft.wp_load_checkQuorum $$ Hphys as Hphys
  have Hctx_ne' : ctx ≠ go!"CampaignTransfer" := Hctx_ne
  rw [decide_eq_false Hctx_ne']
  try wp_auto
  -- neither MsgPreVote nor MsgPreVoteResp, so we fall through to the step-down
  ty_ne 17
  try wp_auto
  ty_ne 18
  try wp_auto
  wp_apply raft.wp_load_id $$ Hphys as Hphys
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  wp_raft_log
  -- a `MsgVote` is not from a leader, so no leader is adopted
  ty_ne 3
  try wp_auto
  ty_ne 8
  try wp_auto
  ty_ne 7
  try wp_auto
  wp_apply _P.becomeFollower cfg r id s m.Term' (W64 0) $$ [$Hphys] as %pvs Hphys
  -- the type switch: not MsgHup / MsgStorageAppendResp / MsgStorageApplyResp, not
  -- MsgPreVote, but MsgVote
  rw [Hty]
  try wp_auto
  -- Stepping down to a strictly greater term cleared both `Vote` and `lead`, so
  -- `canVote` holds
  have Hne : m.Term' ≠ s.term := by intro Heq; rw [Heq] at Hgt0; omega
  obtain ⟨s1, Hs1⟩ : ∃ s1, s1 = { becomeFollower s m.Term' (W64 0) with prvals := pvs } :=
    ⟨_, rfl⟩
  ihave Hphys := ownRaftPhys_eq cfg r id _ s1 Hs1.symm $$ Hphys
  have Hv1 : s1.vote = W64 0 := by
    subst Hs1; simp [becomeFollower, resetTo, Hne]
  have Hl1 : s1.lead = W64 0 := by subst Hs1; rfl
  have Ht1 : s1.term = m.Term' := by subst Hs1; rfl
  have Hwf1 : NStateWf s1 := by subst Hs1; rfl
  have Hps1 : toPState s1 = pbecomeFollower (toPState s) m.Term' (W64 0) := by
    subst Hs1
    exact (toPState_prvals_nl (becomeFollower s m.Term' (W64 0)) pvs
      (by simp [becomeFollower])).trans (toPState_becomeFollower _ _ _)
  wp_apply raft.wp_load_Vote $$ Hphys as Hphys
  rw [Hv1, decide_eq_false (fun h : W64 0 = m.From' => Hfnz h.symm)]
  try wp_auto
  wp_apply raft.wp_load_Vote $$ Hphys as Hphys
  rw [Hv1]
  try wp_auto
  wp_apply raft.wp_load_lead $$ Hphys as Hphys
  rw [Hl1]
  try wp_auto
  -- the two log calls, each on the log taken out of `Hphys` and put back
  wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
  icases ownRaftPhys_log_same $$ Hphys with ⟨Hlog1, Hback⟩
  wp_apply _P.lastEntryID $$ [$Hlog1] as %lastID ⟨Hlog1, -⟩
  ihave Hphys := Hback $$ Hlog1
  try wp_auto
  wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
  icases ownRaftPhys_log_same $$ Hphys with ⟨Hlog1, Hback⟩
  wp_apply _P.isUpToDate $$ [$Hlog1] as %uptodate ⟨Hlog1, %Hutd⟩
  ihave Hphys := Hback $$ Hlog1
  cases uptodate
  all_goals try wp_auto
  all_goals
    wp_apply raft.wp_load_id $$ Hphys as Hphys
    wp_apply raft.wp_load_Vote $$ Hphys as Hphys
    wp_apply raft.wp_load_Term $$ Hphys as Hphys
    wp_raft_log
  · -- the candidate's log is behind: decline, without recording a vote
    wp_apply raft.wp_load_Term $$ Hphys as Hphys
    wp_apply _P.voteRespMsgType m.Type' MsgVoteResp (.inl ⟨Hty, rfl⟩)
    try wp_auto
    let resp : raftpb.Message :=
      { Type' := MsgVoteResp, To' := m.From', From' := 0, Term' := s1.term, LogTerm' := 0,
        Index' := 0, Entries' := slice.nil, Commit' := 0, Vote' := 0, Snapshot' := null,
        Reject' := true, RejectHint' := 0, Context' := slice.nil, Responses' := slice.nil }
    have Hok : SendOk id s1 resp [] [Msg.plain .voteResp id m.From' s1.term true] :=
      Or.inl ⟨.voteResp, Or.inr (Or.inl rfl), rfl, by show s1.term ≠ W64 0; rw [Ht1]; exact Hterm,
        fun Hc => by
          exfalso; change MsgVoteResp = _ ∨ MsgVoteResp = _ at Hc
          rcases Hc with Hc | Hc <;> exact absurd Hc (by w32_ne), rfl⟩
    wp_apply _P.send cfg r id s1 resp [] _ (.inl rfl) Hok $$ [$Hphys] as Hphys
    · isplitr
      · iapply ownSlice_nil
      · iapply send_no_snap
        exact (by w32_ne : MsgVoteResp ≠ MsgSnap)
    iapply HΦ $$ %interface.nil %_
    iframe Hphys
    ipureintro
    refine ⟨nstateWf_sendMsgs _ _ Hwf1, ⟨[absMsg .vote m ents] ++ [absMsg .vote m ents], ?_, ?_⟩, rfl⟩
    · intro m' Hm'; simpa using Hm'
    · rw [toPState_sendMsgs, Hps1, Ht1]
      exact step_stepdown_then_reject cfg id (toPState s) (absMsg .vote m ents) rfl Hto Hgt0
  · -- the candidate's log is up to date: grant the vote
    wp_apply _P.voteRespMsgType m.Type' MsgVoteResp (.inl ⟨Hty, rfl⟩)
    try wp_auto
    let resp : raftpb.Message :=
      { Type' := MsgVoteResp, To' := m.From', From' := 0, Term' := m.Term', LogTerm' := 0,
        Index' := 0, Entries' := slice.nil, Commit' := 0, Vote' := 0, Snapshot' := null,
        Reject' := false, RejectHint' := 0, Context' := slice.nil, Responses' := slice.nil }
    have Hok : SendOk id s1 resp [] [Msg.plain .voteResp id m.From' m.Term' false] :=
      Or.inl ⟨.voteResp, Or.inr (Or.inl rfl), rfl, Hterm,
        fun Hc => by
          exfalso; change MsgVoteResp = _ ∨ MsgVoteResp = _ at Hc
          rcases Hc with Hc | Hc <;> exact absurd Hc (by w32_ne), rfl⟩
    -- `send` the granted vote response, then record the vote
    wp_apply _P.send cfg r id s1 resp [] _ (.inl rfl) Hok $$ [$Hphys] as Hphys
    · isplitr
      · iapply ownSlice_nil
      · iapply send_no_snap
        exact (by w32_ne : MsgVoteResp ≠ MsgSnap)
    -- `m.Type = MsgVote`, so the vote is recorded: `r.Vote := m.From`
    rw [Hty]
    try wp_auto
    wp_apply raft.wp_store_electionElapsed $$ Hphys as Hphys
    wp_apply raft.wp_store_Vote $$ Hphys as Hphys
    iapply HΦ $$ %interface.nil %_
    iframe Hphys
    ipureintro
    refine ⟨Hwf1, ⟨[absMsg .vote m ents] ++ [absMsg .vote m ents], ?_, ?_⟩, rfl⟩
    · intro m' Hm'; simpa using Hm'
    · have H : Step cfg id (toPState s) ([absMsg .vote m ents] ++ [absMsg .vote m ents])
          (psendMsgs { pbecomeFollower (toPState s) m.Term' (W64 0) with vote := m.From' }
            [Msg.plain .voteResp id m.From' m.Term' false]) :=
        step_stepdown_then_vote cfg id (toPState s) (absMsg .vote m ents) rfl Hto Hfnz
        Hgt0 (by subst Hs1; exact Hutd.symm)
      rw [← Hps1] at H
      exact H

end StepProof

end branches

end EtcdGrove
end Perennial
