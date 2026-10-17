/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgVote_gt.v.

One term case of `Step`'s `MsgVote` branch, in its own file so that it checks in
parallel with the other -- see `proof_raft__Step_MsgVote.v` (`MsgVote.lean`), which
combines the two, and `notes/decisions.md` (2026-09-17; 2026-09-18 for why this
directory exists). Proof structure, not specification: no `Module Type`, no
`Parameter`; only `MsgVote.lean` may import this module.

Lean notes:
* The branch lemma takes the callee specs (Rocq's functor argument `P : STEP_POSTULATES`)
  as its first argument `_P : raft.Step.Postulates`, and Rocq's section variable `c`
  as its second.
* Rocq's `Local Ltac recv_elem` (`∀ m' ∈ recv, m' = a` for the concrete `recv` lists
  `[]`, `[a]`, `[a] ++ [a]`, by rewriting the membership away rather than `set_solver`,
  which took 150s and more there) is not ported.
* The type tests `m.Type' = W32 k` (all false: `m` is a `MsgVote`) are the macro
  `ty_ne k` (`ElectionLemmas.lean`).
* After `becomeFollower`, the state `{ becomeFollower s m.Term' (W64 0) with prvals :=
  pvs }` is named `s1` (`ownRaftPhysC_eq`), with its `vote`/`lead`/`term` and its
  `toPState` (`Hps1`) as separate facts: the loads then return `s1.vote` etc., which a
  `rw` can rewrite (on the unnamed record the `decide`'s instance blocks the rewrite).
  The two outcomes end in `stepC_stepdown_then_vote` / `stepC_stepdown_then_reject`
  (`StepLemmas.lean`) rather than `StepC.trans` of the step-down and the answer.

raft v3.7 (2026-10-15, stage R4 phase 3): the message is a pointer `ml` with `msgIn ml □ ⟨m, ents,
sn, ctx, rs⟩` (its `Context`, `ctx`, read by `GetContext` for the leader-transfer test); its fields
are read by the getters (`wp_get`/`wp_gets`, `ElectionLemmas.lean`, by `PB`), and the response is a
fresh `*pb.Message` sharing the request's `From` (and, granted, `Term`) cell
(`msgPtsC_From_acc`/`msgPtsC_Term_acc`, `msgOwn_of_resp`), handed to `send` (`msgOwn`).
-/
module

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
/-- `MsgVote` with `m.Term > r.Term`: step down to follower first, then grant or decline
in the new term. -/
theorem wp_Step_MsgVote_gt (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (PB : raft.Step.PbPostulates (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc) :
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
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
        -- (stage R4) the message, as `Step` received it
        "Hm" ∷ msgIn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        -- `recv` is whatever this branch consumed -- nothing, or the incoming message
        -- once or twice. Naming its elements rather than the list lets
        -- `raft.Step.wp_proof` discharge the `isMessage` side of `ownRaftGhost_step`
        -- from the single fact it holds about `m`.
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absMsg .vote m ents) ∧
            StepCD c id m s recv s'⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ }} := by
  -- `MessageType.Enum()`'s receiver: `int32` is not an interface (as in `toConfChangeSingle`)
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  intro Hty Hto Hterm Hfnz Hgt0 Hwf
  wp_start as ⟨Hphys, Hm⟩
  icases msgPtsC_nn _ _ _ _ _ $$ Hm with ⟨%Hnn, Hm⟩
  wp_auto
  wp_gets
  rw [decide_eq_false Hnn]
  wp_auto
  wp_gets
  wp_apply _P.traceReceiveMessage
  try wp_auto
  wp_apply PB.GetTerm.1 $$ [$Hm] as Hm
  -- `m.Term ≠ 0`, so the first arm of the term preamble is skipped
  wp_gets
  rw [decide_eq_false Hterm]
  wp_auto
  wp_get
  wp_gets
  wp_apply raft.wp_load_TermC $$ Hphys as Hphys
  wp_gets
  rw [decide_eq_true Hgt0]
  wp_auto
  wp_gets
  rw [Hty]
  wp_auto
  -- `force` is false (not a leader transfer) and `inLease` is false (no check-quorum),
  -- so the lease check does not drop the message
  wp_gets
  wp_apply PB.GetContext.1 $$ [$Hm] as %cs ⟨#Hctx_sl, Hm⟩
  wp_apply wp_string_to_bytes as %ct_sl ⟨ct_sl, -⟩
  wp_apply bytes.wp_Equal _ _ DFrac.discard (DFrac.own 1) ctx (go!"CampaignTransfer") $$ [$Hctx_sl $ct_sl]
    as ⟨-, -⟩
  wp_gets
  wp_apply raft.wp_load_checkQuorumC $$ Hphys as Hphys
  -- `force` (2026-10-13): a leader transfer's vote request or not; either way
  -- `!force && inLease` is false, `inLease` being false without check-quorum
  by_cases Hforce : ctx = go!"CampaignTransfer"
  wp_gets
  rw [decide_eq_true Hforce]
  try wp_auto
  rotate_left
  wp_gets
  rw [decide_eq_false Hforce]
  try wp_auto
  all_goals
    -- neither MsgPreVote nor MsgPreVoteResp, so we fall through to the step-down
    ty_ne 17
    try wp_auto
    ty_ne 18
    try wp_auto
    wp_gets
    wp_apply raft.wp_load_idC $$ Hphys as Hphys
    wp_gets
    wp_apply raft.wp_load_TermC $$ Hphys as Hphys
    wp_gets
    wp_raft_logC
    -- a `MsgVote` is not from a leader, so no leader is adopted
    ty_ne 3
    try wp_auto
    ty_ne 8
    try wp_auto
    ty_ne 7
    try wp_auto
    wp_gets
    wp_apply _P.becomeFollower c r id s m.Term' (W64 0) (Int.le_of_lt Hgt0) $$ [$Hphys] as %pvs Hphys
    -- the type switch: not MsgHup / MsgStorageAppendResp / MsgStorageApplyResp, not
    -- MsgPreVote, but MsgVote
    wp_gets
    rw [Hty]
    try wp_auto
    -- Stepping down to a strictly greater term cleared both `Vote` and `lead`, so
    -- `canVote` holds
    have Hne : m.Term' ≠ s.term := by intro Heq; rw [Heq] at Hgt0; omega
    obtain ⟨s1, Hs1⟩ : ∃ s1, s1 = { becomeFollower s m.Term' (W64 0) with prvals := pvs } :=
      ⟨_, rfl⟩
    ihave Hphys := ownRaftPhysC_eq c r id _ s1 Hs1.symm $$ Hphys
    have Hv1 : s1.vote = W64 0 := by
      subst Hs1; simp [becomeFollower, resetTo, resetTo0, Hne]
    have Hl1 : s1.lead = W64 0 := by subst Hs1; rfl
    have Ht1 : s1.term = m.Term' := by subst Hs1; rfl
    have Hwf1 : NStateWf s1 := by subst Hs1; exact ⟨rfl, rfl⟩
    have Hps1 : toPState s1 = pbecomeFollower (toPState s) m.Term' (W64 0) := by
      subst Hs1
      exact (toPState_prvals_nl (becomeFollower s m.Term' (W64 0)) pvs
        (by simp [becomeFollower])).trans (toPState_becomeFollower _ _ _)
    wp_gets
    wp_apply raft.wp_load_VoteC $$ Hphys as Hphys
    wp_gets
    rw [Hv1, decide_eq_false (fun h : W64 0 = m.From' => Hfnz h.symm)]
    try wp_auto
    wp_gets
    wp_apply raft.wp_load_VoteC $$ Hphys as Hphys
    wp_gets
    rw [Hv1]
    try wp_auto
    wp_gets
    wp_apply raft.wp_load_leadC $$ Hphys as Hphys
    wp_gets
    rw [Hl1]
    try wp_auto
    -- the two log calls, each on the log taken out of `Hphys` and put back
    wp_gets
    wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
    icases ownRaftPhysC_log_same $$ Hphys with ⟨Hlog1, Hback⟩
    wp_gets
    wp_apply _P.lastEntryID $$ [$Hlog1] as %lastID ⟨Hlog1, -⟩
    ihave Hphys := Hback $$ Hlog1
    try wp_auto
    wp_gets
    wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
    icases ownRaftPhysC_log_same $$ Hphys with ⟨Hlog1, Hback⟩
    wp_gets
    wp_apply _P.isUpToDate $$ [$Hlog1] as %uptodate ⟨Hlog1, %Hutd⟩
    ihave Hphys := Hback $$ Hlog1
    cases uptodate
    all_goals try wp_auto
    all_goals
      wp_gets
      wp_apply raft.wp_load_idC $$ Hphys as Hphys
      wp_gets
      wp_apply raft.wp_load_VoteC $$ Hphys as Hphys
      wp_gets
      wp_apply raft.wp_load_TermC $$ Hphys as Hphys
      wp_gets
      wp_raft_logC
    · -- the candidate's log is behind: decline, without recording a vote
      icases msgPtsC_From_acc _ _ _ _ _ $$ Hm with ⟨%pfr, HFr, #cFr, HmB⟩
      wp_load
      ihave Hm := HmB $$ HFr
      try wp_auto
      wp_apply raft.wp_load_TermC $$ Hphys as Hphys
      try wp_auto
      wp_gets
      wp_apply _P.voteRespMsgType m.Type' MsgVoteResp (.inl ⟨Hty, rfl⟩)
      try wp_auto
      wp_apply PB.Enum MsgVoteResp
      iintro %pty Hpty
      wp_auto
      -- the response `&pb.Message{To: m.From, Term: new(r.Term), Type: .., Reject: new(true)}`
      imod cellRO_alloc _ _ $$ Hpty with #cTy
      imod cellRO_alloc _ _ $$ «$v1» with #cTe
      imod cellRO_alloc _ _ $$ «$v3» with #cRj
      imod msgOwn_of_resp _ _ _ _ _ MsgVoteResp m.From' s1.term true ⊤ $$ [«$a0»] with Hresp
      · iframe «$a0» cTy cFr cTe cRj
      let resp : MessageM :=
        ⟨MsgVoteResp, m.From', W64 0, s1.term, W64 0, W64 0, W64 0, W64 0, true, W64 0⟩
      have Hok : SendOk id s1 resp [] [] [Msg.plain .voteResp id m.From' s1.term true] :=
        Or.inl ⟨.voteResp, Or.inr (Or.inl rfl), rfl, by show s1.term ≠ W64 0; rw [Ht1]; exact Hterm,
          fun Hc => by
            exfalso; change MsgVoteResp = _ ∨ MsgVoteResp = _ at Hc
            rcases Hc with Hc | Hc <;> exact absurd Hc (by w32_ne),
          fun _ => ⟨rfl, rfl, by show uint.Z s1.term ≤ _; split <;> omega⟩,
          fun _ => ⟨Int.le_refl _, (by w32_ne : MsgVoteResp ≠ MsgPreVoteResp)⟩, rfl⟩
      wp_apply _P.send c r id s1 «$a0_ptr» resp [] none [] [] _ (.inl rfl) Hok
        (fun h => absurd h (by show MsgVoteResp ≠ MsgSnap; w32_ne)) $$ [$Hphys $Hresp] as Hphys
      iapply HΦ $$ %interface.nil %_
      iframe Hphys
      ipureintro
      refine ⟨nstateWf_sendMsgs _ _ Hwf1, ⟨[absMsg .vote m ents] ++ [absMsg .vote m ents], ?_, ?_⟩,
        rfl, stepdown_frame' (by rw [Hty]; w32_ne) Hgt0 Hs1 rfl rfl⟩
      · intro m' Hm'; simpa using Hm'
      · refine StepCD.frame ?_ (by subst Hs1; rframe)
        wp_gets
        rw [toPState_sendMsgs, Hps1, Ht1]
        exact stepCF_stepdown_then_reject c id (toPState s) (absMsg .vote m ents) rfl Hto Hgt0
    · -- the candidate's log is up to date: grant the vote
      icases msgPtsC_From_acc _ _ _ _ _ $$ Hm with ⟨%pfr, HFr, #cFr, HmB⟩
      wp_load
      ihave Hm := HmB $$ HFr
      try wp_auto
      icases msgPtsC_Term_acc _ _ _ _ _ $$ Hm with ⟨%pte, HTe, #cTe, HmB⟩
      wp_load
      ihave Hm := HmB $$ HTe
      try wp_auto
      wp_gets
      wp_apply _P.voteRespMsgType m.Type' MsgVoteResp (.inl ⟨Hty, rfl⟩)
      try wp_auto
      wp_apply PB.Enum MsgVoteResp
      iintro %pty Hpty
      wp_auto
      -- the response `&pb.Message{To: m.From, Term: m.Term, Type: ..}`: the request's cells
      imod cellRO_alloc _ _ $$ Hpty with #cTy
      ihave #cRj : cellRO (GF := GF) null false $$ []
      · iapply (show ⊢ cellRO (GF := GF) null false from cellRO_null (V := Bool))
      imod msgOwn_of_resp _ _ _ _ _ MsgVoteResp m.From' m.Term' false ⊤ $$ [«$a0»] with Hresp
      · iframe «$a0» cTy cFr cTe cRj
      let resp : MessageM :=
        ⟨MsgVoteResp, m.From', W64 0, m.Term', W64 0, W64 0, W64 0, W64 0, false, W64 0⟩
      have Hok : SendOk id s1 resp [] [] [Msg.plain .voteResp id m.From' m.Term' false] :=
        Or.inl ⟨.voteResp, Or.inr (Or.inl rfl), rfl, Hterm,
          fun Hc => by
            exfalso; change MsgVoteResp = _ ∨ MsgVoteResp = _ at Hc
            rcases Hc with Hc | Hc <;> exact absurd Hc (by w32_ne),
          fun _ => ⟨rfl, rfl, by show uint.Z m.Term' ≤ _; rw [Ht1]; split <;> omega⟩,
          fun _ => ⟨by show uint.Z m.Term' ≤ _; rw [Ht1]; exact Int.le_refl _, (by w32_ne : MsgVoteResp ≠ MsgPreVoteResp)⟩, rfl⟩
      -- `send` the granted vote response, then record the vote
      wp_apply _P.send c r id s1 «$a0_ptr» resp [] none [] [] _ (.inl rfl) Hok
        (fun h => absurd h (by show MsgVoteResp ≠ MsgSnap; w32_ne)) $$ [$Hphys $Hresp] as Hphys
      -- `m.Type = MsgVote`, so the vote is recorded: `r.Vote := m.From`
      wp_gets
      rw [Hty]
      try wp_auto
      wp_gets
      wp_apply raft.wp_store_electionElapsedC $$ Hphys as Hphys
      wp_gets
      wp_apply raft.wp_store_VoteC $$ Hphys as Hphys
      iapply HΦ $$ %interface.nil %_
      iframe Hphys
      ipureintro
      refine ⟨Hwf1, ⟨[absMsg .vote m ents] ++ [absMsg .vote m ents], ?_, ?_⟩, rfl,
        stepdown_frame' (by rw [Hty]; w32_ne) Hgt0 Hs1 rfl rfl⟩
      · intro m' Hm'; simpa using Hm'
      · refine StepCD.frame ?_ (by subst Hs1; exact ⟨rfl, rfl, fun h => absurd h (by simp [becomeFollower])⟩)
        have H : StepCF c id (toPState s) ([absMsg .vote m ents] ++ [absMsg .vote m ents])
            (psendMsgs { pbecomeFollower (toPState s) m.Term' (W64 0) with vote := m.From' }
              [Msg.plain .voteResp id m.From' m.Term' false]) :=
          stepCF_stepdown_then_vote c id (toPState s) (absMsg .vote m ents) rfl Hto Hfnz
          Hgt0 (by subst Hs1; exact Hutd.symm)
        wp_gets
        rw [← Hps1] at H
        exact H

end StepProof

end branches

end EtcdGrove
end Perennial
