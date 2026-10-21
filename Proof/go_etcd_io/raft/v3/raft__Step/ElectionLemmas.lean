/- The election branches' own helpers for `Step`'s proof (raft v3.7 retarget, stage R4 phase 3,
group G4a).

`raft.Step.Postulates` (`Base.lean`) bundles the callee specs of `raft.go`; since v3.7 `Step`
also reads the message through its protobuf getters (`m.GetTerm()`, ...) and builds responses
with `MessageType.Enum()`, whose specs (R1, `Spec/.../raftpb/`) are bundled here as
`raft.Step.PbPostulates`, which the election branch lemmas take beside `raft.Step.Postulates`.

Also the tactic macros shared by the branch files split for parallel checking (`MsgVote_eq_*`,
`MsgVote_gt`: `ty_ne`, `vote_grant_tail`, `vote_reject_tail`; `MsgPreVote_eq`/`_gt`: `cv_step`,
`prevote_resp_tail`; `MsgPreVoteResp_eq`/`_gt`: `prevote_resp_dispatch`). They are written with
`hygiene false` and refer to the caller's hypotheses and to lemmas the caller imports
(`prevote_lemmas.lean`'s `*StepResult_prevoteresp`).
-/
module

public import Proof.go_etcd_io.raft.v3.raft__Step.Base
public import Proof.go_etcd_io.raft.v3.InvPbMsg
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTerm
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetFrom
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetLogTerm
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetReject
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetContext
public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section base
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The protobuf specs `Step`'s election branches use (stage R4): the message getters and
`MessageType.Enum`. -/
structure raft.Step.PbPostulates : Prop where
  GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG)
  GetTerm : raftpb.Message.GetTerm.spec (GF := GF) (hG := hG)
  GetFrom : raftpb.Message.GetFrom.spec (GF := GF) (hG := hG)
  GetLogTerm : raftpb.Message.GetLogTerm.spec (GF := GF) (hG := hG)
  GetIndex : raftpb.Message.GetIndex.spec (GF := GF) (hG := hG)
  GetReject : raftpb.Message.GetReject.spec (GF := GF) (hG := hG)
  GetContext : raftpb.Message.GetContext.spec (GF := GF) (hG := hG)
  Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)

/-- The request's `Term` cell, for a response built with `Term: m.Term`. -/
theorem msgPtsC_Term_acc (l : Loc) (dq dqe : DFrac) (cap : Bool) (ms : MsgSt) :
    msgPtsC (GF := GF) l dq dqe cap ms ⊢
      ∃ p : Loc, l.[raftpb.Message, go!"Term"] ↦{dq} p ∗ cellRO p ms.msg.Term' ∗
        (l.[raftpb.Message, go!"Term"] ↦{dq} p -∗ msgPtsC l dq dqe cap ms) := by
  iintro H
  iNamed H
  iexists pte
  iframe HTe cTe
  iintro HTe
  iunfold msgPtsC
  iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, ps, cs, rs, uf
  isplitr
  · ipureintro; exact Hnn
  iframe
  iframe cTy cTo cFr cTe cLt cIx cCo cVo cRj cRh Hents Hcs Hpb

/-- The struct of `&pb.Message{To: .., Term: .., Type: .., Reject: ..}`. -/
abbrev respStruct (pty pto pte prj : Loc) : raftpb.Message :=
  { state' := zeroValDef, Type' := pty, To' := pto, From' := null,
    Term' := pte, LogTerm' := null, Index' := null, Entries' := slice.nil, Commit' := null,
    Vote' := null, Snapshot' := null, Reject' := prj, RejectHint' := null,
    Context' := slice.nil, Responses' := slice.nil, unknownFields' := slice.nil,
    sizeCache' := 0 }

/-- A response raft builds, `&pb.Message{To: .., Term: .., Type: .., Reject: ..}` (each set
field a cell; `Term`/`Reject` may be unset, `null`), is an owned message without entries,
snapshot, context or responses. -/
theorem msgOwn_of_resp (l pty pto pte prj : Loc) (ty : raftpb.MessageType) (to te : w64)
    (rj : Bool) (E : CoPset) :
    (l ↦ respStruct pty pto pte prj ∗
      cellRO pty ty ∗ cellRO pto to ∗ cellRO pte te ∗ cellRO prj rj : IProp GF) ⊢
      |={E}=> msgOwn l (DFrac.own 1)
        ⟨⟨ty, to, W64 0, te, W64 0, W64 0, W64 0, W64 0, rj, W64 0⟩, [], none, [], []⟩ := by
  iintro ⟨Hl, #cTy, #cTo, #cTe, #cRj⟩
  iapply (msgOwn_of_struct l (respStruct pty pto pte prj) [] _ E rfl)
  dsimp only
  iframe Hl
  iframe cTy cTo cTe cRj
  ihave #Hn64 : cellRO (GF := GF) null (W64 0) $$ []
  · iapply (show ⊢ cellRO (GF := GF) null (W64 0) from cellRO_null (V := w64))
  iframe Hn64
  isplitr
  · iapply ownSlice_nil
  isplitr
  · iapply BigSepL2.bigSepL2_nil.2; ipureintro; trivial
  isplitr
  · simp only [snapOpt]; ipureintro; trivial
  isplitr
  · iapply ownSlice_nil
  iapply ownSlice_nil

omit ffi [FfiInterp ffi] [FfiSemantics ext ffi] go_gctx in
/-- `send`'s premise for the vote response the `MsgVote` tails build (`Term: term`,
`Reject: rej`). -/
theorem sendOk_voteResp (id : w64) (s : NState) (to term : w64) (rej : Bool)
    (Ht : term ≠ W64 0) (Hle : uint.Z term ≤ uint.Z s.term) :
    SendOk id s
      ⟨MsgVoteResp, to, W64 0, term, W64 0, W64 0, W64 0, W64 0, rej, W64 0⟩
      [] [] [Msg.plain .voteResp id to term rej] :=
  Or.inl ⟨.voteResp, Or.inr (Or.inl rfl), rfl, Ht,
    fun Hc => by
      exfalso; change MsgVoteResp = _ ∨ MsgVoteResp = _ at Hc
      rcases Hc with Hc | Hc <;> exact absurd Hc (by w32_ne),
    fun _ => ⟨rfl, rfl, Int.le_trans Hle (by split <;> omega)⟩, .inl Hle, rfl⟩

end base

set_option hygiene false in
/-- A getter call on the message `Hm`, by the specs `PB : raft.Step.PbPostulates` (both names
the caller's). -/
macro "wp_get" : tactic =>
  `(tactic| first
    | (wp_apply PB.GetTerm.1 $$ [Hm] as Hm; iexact Hm)
    | (wp_apply PB.GetType.1 $$ [Hm] as Hm; iexact Hm)
    | (wp_apply PB.GetFrom.1 $$ [Hm] as Hm; iexact Hm)
    | (wp_apply PB.GetLogTerm.1 $$ [Hm] as Hm; iexact Hm)
    | (wp_apply PB.GetIndex.1 $$ [Hm] as Hm; iexact Hm)
    | (wp_apply PB.GetReject.1 $$ [Hm] as Hm; iexact Hm))

/-- Every getter call (`wp_get`) and pure step up to the next other call or undecided test. -/
macro "wp_gets" : tactic => `(tactic| repeat (wp_get; try wp_auto))

set_option hygiene false in
/-- (2026-10-17, `CheckQuorum` on) `Step`'s lease check on a `MsgVote`/`MsgPreVote` of a higher
term, from the load of `r.checkQuorum` on (`force`, the message's `Context` the transfer marker
or not, is `Hforce`'s):

    inLease := r.checkQuorum && r.lead != None && r.electionElapsed < r.electionTimeout
    if !force && inLease { r.logger.Infof(...); return nil }

Split on `r.checkQuorum` (`Hcq`), the leader and the election timer, then on `force`. Where the
message is ignored (`checkQuorum` on, a leader known, within the timeout, not forced) the step is
`StepC.refl`, closed here; every other goal is left at the code after the check, `inLease`
having been false or the request forced. -/
macro "wp_lease_check " cx:term : tactic => `(tactic| (
  wp_apply Perennial.EtcdGrove.raft.wp_load_checkQuorumC $$ Hphys as Hphys
  cases Hcq : s.cq
  all_goals try wp_auto
  all_goals try (
    have _ : s.cq = true := Hcq
    wp_apply Perennial.EtcdGrove.raft.wp_load_leadC $$ Hphys as Hphys
    try wp_auto
    wp_if_destruct)
  all_goals try (
    have _ : s.cq = true := Hcq
    wp_apply Perennial.EtcdGrove.raft.wp_load_electionElapsedC $$ Hphys as %ee Hphys
    try wp_auto
    wp_apply Perennial.EtcdGrove.raft.wp_load_electionTimeoutC $$ Hphys as %et ⟨Hphys, %Het⟩
    try wp_auto)
  all_goals by_cases Hforce : $cx = go!"CampaignTransfer"
  all_goals (
    wp_gets
    try (first | rw [decide_eq_true Hforce] | rw [decide_eq_false Hforce])
    try wp_auto)
  -- not forced, a leader known: the timer decides
  all_goals try (
    have _ : s.cq = true := Hcq
    have _ : ¬ $cx = go!"CampaignTransfer" := Hforce
    have _ : ¬ s.lead = W64 0 := Hif
    wp_if_destruct)
  -- ignored within the lease: `lastEntryID` for the log line, then `nil`
  all_goals try (
    wp_apply Perennial.EtcdGrove.raft.wp_load_raftLogC $$ Hphys as Hphys
    icases Perennial.EtcdGrove.ownRaftPhysC_log_same $$ Hphys with ⟨Hlog1, Hback⟩
    wp_gets
    wp_apply _P.lastEntryID $$ [Hlog1] as %lastID ⟨Hlog1, -⟩
    · iframe
    ihave Hphys := Hback $$ Hlog1
    try wp_auto
    repeat (first
      | (wp_get; try wp_auto)
      | (wp_apply Perennial.EtcdGrove.raft.wp_load_idC $$ Hphys as Hphys; try wp_auto)
      | (wp_apply Perennial.EtcdGrove.raft.wp_load_VoteC $$ Hphys as Hphys; try wp_auto)
      | (wp_apply Perennial.EtcdGrove.raft.wp_load_TermC $$ Hphys as Hphys; try wp_auto)
      | (wp_apply Perennial.EtcdGrove.raft.wp_load_electionTimeoutC $$ Hphys as %et' ⟨Hphys, -⟩;
         try wp_auto)
      | (wp_apply Perennial.EtcdGrove.raft.wp_load_electionElapsedC $$ Hphys as %ee' Hphys;
         try wp_auto))
    wp_raft_logC
    iapply HΦ $$ %interface.nil %s
    iframe Hphys
    ipureintro
    first
      | exact ⟨Hwf, ⟨[], fun _ H => absurd H List.not_mem_nil,
          Perennial.EtcdGrove.StepCD.frame (.refl _) (Perennial.EtcdGrove.RFrame.refl _)⟩, rfl,
          Perennial.EtcdGrove.StepProof.keep_frame rfl rfl rfl rfl rfl⟩
      | exact ⟨Hwf, Perennial.EtcdGrove.StepCD.frame (.refl _) (Perennial.EtcdGrove.RFrame.refl _),
          rfl, Perennial.EtcdGrove.StepProof.keep_frame rfl rfl rfl rfl rfl⟩)))

set_option hygiene false in
/-- (2026-10-17, `CheckQuorum` on) `Step`'s `r.checkQuorum || r.preVote`, in the stale-term arm:
both loads, split on both flags -- `checkQuorum` off with pre-vote off, off with pre-vote on, and
on (the `||` short-circuits) -- each run past the `||`. -/
macro "wp_cq_pv" : tactic => `(tactic| (
  wp_apply Perennial.EtcdGrove.raft.wp_load_checkQuorumC $$ Hphys as Hphys
  cases s.cq
  all_goals try wp_auto
  all_goals try (
    wp_gets
    wp_apply Perennial.EtcdGrove.raft.wp_load_preVoteC $$ Hphys as Hphys
    cases s.prevote)
  all_goals try wp_auto))

set_option hygiene false in
/-- `m.Type' = W32 k` is false: `m` is a `MsgVote` (`Hty`). -/
macro "ty_ne " k:num : tactic =>
  `(tactic| (wp_gets; rw [decide_eq_false (show m.Type' ≠ W32 $k by rw [Hty]; w32_ne)]))

set_option hygiene false in
/-- Rocq `vote_grant_tail`: log, `send` the response, record `r.Vote := m.From`
(`StepC.grantVote`). Needs `Hcan : PCanVote (toPState s) m.From'` and
`Hutd : true = plogUpToDate …` in scope, and `Heq0 : m.Term' = s.term`. -/
macro "vote_grant_tail" : tactic => `(tactic| (
  try wp_auto
  wp_gets
  wp_apply raft.wp_load_idC $$ Hphys as Hphys
  wp_gets
  wp_apply raft.wp_load_VoteC $$ Hphys as Hphys
  wp_gets
  wp_apply raft.wp_load_TermC $$ Hphys as Hphys
  wp_gets
  wp_raft_logC
  -- the response `&pb.Message{To: m.From, Term: m.Term, Type: ..}`: the request's cells
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
  imod cellRO_alloc _ _ $$ Hpty with #cTy
  ihave #cRj : cellRO (GF := GF) null false $$ []
  · iapply (show ⊢ cellRO (GF := GF) null false from cellRO_null (V := Bool))
  imod msgOwn_of_resp _ _ _ _ _ MsgVoteResp m.From' m.Term' false ⊤ $$ [«$a0»] with Hresp
  · iframe «$a0» cTy cFr cTe cRj
  wp_apply _P.send c r id s «$a0_ptr» _ [] none [] [] _ (.inl rfl)
      (sendOk_voteResp id s m.From' m.Term' false Hterm
        (Int.le_of_eq (congrArg (fun x : w64 => uint.Z x) Heq0)))
      (fun h => absurd h (by show MsgVoteResp ≠ MsgSnap; w32_ne)) $$ [Hphys Hresp] as Hphys
  · iframe
  wp_gets
  rw [Hty]
  try wp_auto
  -- `r.electionElapsed = 0; r.Vote = m.From`
  wp_gets
  wp_apply raft.wp_store_electionElapsedC $$ Hphys as Hphys
  wp_gets
  wp_apply raft.wp_store_VoteC $$ Hphys as Hphys
  iapply HΦ $$ %interface.nil %_
  iframe Hphys
  ipureintro
  refine ⟨Hwf, ⟨[absMsg .vote m ents], fun m' Hm' => by simpa using Hm', ?_⟩, rfl,
    keep_frame rfl rfl rfl rfl rfl⟩
  refine StepCD.frame ?_ (by rframe)
  have H : StepCF c id (toPState s) [absMsg .vote m ents]
      (psendMsgs { toPState s with vote := m.From' }
        [Msg.plain .voteResp id m.From' s.term false]) :=
    StepCF.grantVote (absMsg .vote m ents) (toPState s) rfl Hto Hfnz Heq0 Hcan Hutd.symm
  rw [← Heq0] at H
  exact H))

set_option hygiene false in
/-- Rocq `vote_reject_tail`: log, then `send` a rejection carrying `r.Term`
(`StepC.rejectVote`). Always legal. -/
macro "vote_reject_tail" : tactic => `(tactic| (
  try wp_auto
  wp_gets
  wp_apply raft.wp_load_idC $$ Hphys as Hphys
  wp_gets
  wp_apply raft.wp_load_VoteC $$ Hphys as Hphys
  wp_gets
  wp_apply raft.wp_load_TermC $$ Hphys as Hphys
  wp_gets
  wp_raft_logC
  -- the response `&pb.Message{To: m.From, Term: new(r.Term), Type: .., Reject: new(true)}`
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
  imod cellRO_alloc _ _ $$ Hpty with #cTy
  imod cellRO_alloc _ _ $$ «$v1» with #cTe
  imod cellRO_alloc _ _ $$ «$v3» with #cRj
  imod msgOwn_of_resp _ _ _ _ _ MsgVoteResp m.From' s.term true ⊤ $$ [«$a0»] with Hresp
  · iframe «$a0» cTy cFr cTe cRj
  -- the response carries `s.term`, so `send`'s `m.Term ≠ 0` premise is the incoming
  -- message's, transported along `m.Term = s.term`
  wp_apply _P.send c r id s «$a0_ptr» _ [] none [] [] _ (.inl rfl)
      (sendOk_voteResp id s m.From' s.term true (Heq0 ▸ Hterm)
        (Int.le_refl _))
      (fun h => absurd h (by show MsgVoteResp ≠ MsgSnap; w32_ne)) $$ [Hphys Hresp] as Hphys
  · iframe
  iapply HΦ $$ %interface.nil %_
  iframe Hphys
  ipureintro
  exact ⟨Hwf, ⟨[absMsg .vote m ents], fun m' Hm' => by simpa using Hm',
    StepCD.frame (StepCF.rejectVote (absMsg .vote m ents) (toPState s) rfl Hto) (by rframe)⟩, rfl,
    keep_frame rfl rfl rfl rfl rfl⟩))

set_option hygiene false in
/-- Rocq `cv_step`: one step of `canVote`'s evaluation, whatever its outcome: a field
load, or a comparison decided by case analysis. Works on `Hphys`. -/
macro "cv_step" : tactic =>
  `(tactic| first
    | wp_auto
    | wp_get
    | wp_apply Perennial.EtcdGrove.raft.wp_load_VoteC $$ Hphys as Hphys
    | wp_apply Perennial.EtcdGrove.raft.wp_load_leadC $$ Hphys as Hphys
    | wp_apply Perennial.EtcdGrove.raft.wp_load_TermC $$ Hphys as Hphys
    | wp_if_destruct)

set_option hygiene false in
/-- The answer's tail, granted (`grant`: the response `&pb.Message{To: m.From, Term: m.Term,
Type: ..}`, the request's cells) or rejected (the response `&pb.Message{To: m.From, Term:
new(r.Term), Type: .., Reject: new(true)}`): the log call, `voteRespMsgType`, `send`, and
the `MsgVote` test, then `StepC.sendFree`. Uses `Hphys`, `Hm`, `PB`, `HΦ`, `Hty`, `Hwf`, and
the answer's term being nonzero as `Hterm` (a grant at `m.Term`) or `Hs0` (a rejection at
`r.Term`). -/
macro "prevote_resp_tail " grant:ident : tactic =>
  `(tactic| (
    wp_gets
    wp_apply Perennial.EtcdGrove.raft.wp_load_idC $$ Hphys as Hphys
    wp_gets
    wp_apply Perennial.EtcdGrove.raft.wp_load_VoteC $$ Hphys as Hphys
    wp_gets
    wp_apply Perennial.EtcdGrove.raft.wp_load_TermC $$ Hphys as Hphys
    wp_gets
    wp_raft_logC
    icases msgPtsC_From_acc _ _ _ _ _ $$ Hm with ⟨%pfr, HFr, #cFr, HmB⟩
    wp_load
    ihave Hm := HmB $$ HFr
    try wp_auto
    first
    | (have _h : $grant = true := rfl
       icases msgPtsC_Term_acc _ _ _ _ _ $$ Hm with ⟨%pte, HTe, #cTe, HmB⟩
       wp_load
       ihave Hm := HmB $$ HTe
       try wp_auto
       wp_gets
       wp_apply _P.voteRespMsgType m.Type' _ (.inr ⟨Hty, rfl⟩)
       try wp_auto
       wp_apply PB.Enum MsgPreVoteResp
       iintro %pty Hpty
       wp_auto
       imod cellRO_alloc _ _ $$ Hpty with #cTy
       ihave #cRj : cellRO (GF := GF) null false $$ []
       · iapply (show ⊢ cellRO (GF := GF) null false from cellRO_null (V := Bool))
       imod msgOwn_of_resp _ _ _ _ _ MsgPreVoteResp m.From' m.Term' false ⊤ $$ [«$a0»] with Hresp
       · iframe «$a0» cTy cFr cTe cRj
       wp_gets
       wp_apply _P.send c r id s «$a0_ptr»
           ⟨MsgPreVoteResp, m.From', W64 0, m.Term', W64 0, W64 0, W64 0, W64 0, false, W64 0⟩
           [] none [] [] _ (Or.inl rfl)
           (Or.inl ⟨.preVoteResp, Or.inr (Or.inr (Or.inr rfl)), mtypeOf_MsgPreVoteResp,
             Hterm,
             fun Hc => by
               change MsgPreVoteResp = _ ∨ MsgPreVoteResp = _ at Hc
               rcases Hc with Hc | Hc <;> exact absurd Hc (by w32_ne),
             fun h => absurd h Hfid,
             -- (2026-10-17) the requester's term: the node's or within the ceiling
             (by first | exact .inr Hptc | exact .inl (Int.le_of_eq (congrArg _ Heq0))), rfl⟩)
           (fun h => absurd h (by show MsgPreVoteResp ≠ MsgSnap; w32_ne))
         $$ [Hphys Hresp]
       · iframe Hphys Hresp
       iintro Hphys)
    | (have _h : $grant = false := rfl
       wp_apply Perennial.EtcdGrove.raft.wp_load_TermC $$ Hphys as Hphys
       try wp_auto
       wp_gets
       wp_apply _P.voteRespMsgType m.Type' _ (.inr ⟨Hty, rfl⟩)
       try wp_auto
       wp_apply PB.Enum MsgPreVoteResp
       iintro %pty Hpty
       wp_auto
       imod cellRO_alloc _ _ $$ Hpty with #cTy
       imod cellRO_alloc _ _ $$ «$v1» with #cTe
       imod cellRO_alloc _ _ $$ «$v3» with #cRj
       imod msgOwn_of_resp _ _ _ _ _ MsgPreVoteResp m.From' s.term true ⊤ $$ [«$a0»] with Hresp
       · iframe «$a0» cTy cFr cTe cRj
       wp_gets
       wp_apply _P.send c r id s «$a0_ptr»
           ⟨MsgPreVoteResp, m.From', W64 0, s.term, W64 0, W64 0, W64 0, W64 0, true, W64 0⟩
           [] none [] [] _ (Or.inl rfl)
           (Or.inl ⟨.preVoteResp, Or.inr (Or.inr (Or.inr rfl)), mtypeOf_MsgPreVoteResp,
             Hs0,
             fun Hc => by
               change MsgPreVoteResp = _ ∨ MsgPreVoteResp = _ at Hc
               rcases Hc with Hc | Hc <;> exact absurd Hc (by w32_ne),
             fun h => absurd h Hfid,
             .inl (Int.le_refl _), rfl⟩)
           (fun h => absurd h (by show MsgPreVoteResp ≠ MsgSnap; w32_ne))
         $$ [Hphys Hresp]
       · iframe Hphys Hresp
       iintro Hphys)
    try wp_auto
    -- not a `MsgVote`: no vote recorded
    wp_gets
    try (rw [decide_eq_false (show m.Type' ≠ W32 5 by rw [Hty]; w32_ne)]; wp_auto)
    iapply HΦ $$ %interface.nil %_
    iframe Hphys
    ipureintro
    refine ⟨nstateWf_sendMsgs _ _ Hwf, StepCD.frame ?_ (by rframe), rfl,
      keep_frame rfl rfl rfl rfl rfl⟩
    rw [toPState_sendMsgs]
    exact .sendFree _ _ (.inr rfl) rfl))

set_option hygiene false in
/-- `r.step(m)` on a `MsgPreVoteResp` (`MsgPreVoteResp_eq.lean`, `_gt.lean`), by role (Rocq: the four
role cases, each with `wp_load_step`): `stepFollower` and `stepLeader` have no arm for
it; `stepCandidate` ignores it at a candidate and tallies it at a pre-candidate
(`candidateStepResult_prevoteresp`, `prevote_lemmas.lean`). Consumes nothing. Uses `Hphys`, `HΦ`, `Hty`,
`Hwf`, `Hcfg`, `Hnw`. -/
macro "prevote_resp_dispatch" : tactic =>
  `(tactic| (
    wp_gets
    wp_apply Perennial.EtcdGrove.raft.wp_load_stepC $$ Hphys as Hphys
    icases Perennial.EtcdGrove.ownRaftPhysC_voter c r id s $$ Hphys with ⟨%Hvoter, Hphys⟩
    rw [show s.stepfn = stepFuncOf s.role from Hwf.1]
    -- (stage R4) the message as the callees take it: read-only entries (not a proposal)
    have Hnp : ¬ m.Type' = MsgProp := by rw [Hty]; w32_ne
    cases Hrole : s.role
    · -- Follower: no arm
      simp only [stepFuncOf]
      wp_apply _P.stepFollower c ∅ r id s ml m ents sn rs (zero_val _) ctx
          (.inr (.inr (.inr (.inr (.inr (.inr (.inl Hty)))))))
          (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
          (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
          (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
          (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
          (fun Hc => by exfalso; rcases Hc with Hc | Hc <;> rw [Hty] at Hc <;> exact absurd Hc (by w32_ne))
          (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        $$ [Hphys Hm] as %err %s1 %dropped %c1 ⟨Hphys, %Hres, Herrn⟩
      · iframe Hphys; rw [ite_eq_right Hnp]; iexact Hm
      obtain ⟨rfl, rfl, rfl⟩ := followerStepResult_prevoteresp _ _ _ _ _ _ _ _ _ Hty Hres
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Herrn with %Herrn
      subst Herrn
      try wp_auto
      iapply HΦ $$ %interface.nil %_
      iframe Hphys
      ipureintro
      exact ⟨Hwf, ⟨[], fun _ h => absurd h List.not_mem_nil, StepCD.frame (.refl _) (RFrame.refl _)⟩, rfl,
      RespStep.refl _ _, keep_frame rfl rfl rfl rfl rfl⟩
    · -- Candidate: `myVoteRespType` is `MsgVoteResp`; a stale pre-vote response is
      -- ignored
      simp only [stepFuncOf]
      wp_apply _P.stepCandidate c ∅ r id s ml m ents sn rs (zero_val _) ctx
          (.inr (.inr (.inr (.inr (.inr (.inr (.inl Hty)))))))
          (fun Hc => by
            exfalso; rw [Hty] at Hc
            rcases Hc with Hc | Hc | Hc | Hc <;> exact absurd Hc (by w32_ne))
          (.inl Hrole)
          (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
          (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
          (fun Hp _ => Hnw Hp)
          (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        $$ [Hphys Hm] as %err %s1 %dropped %c1 ⟨Hphys, %Hres, Herrn⟩
      · iframe Hphys; rw [ite_eq_right Hnp]; iexact Hm
      obtain ⟨rfl, rfl, Hwf1, Hst, Hresp, Hft⟩ :=
        candidateStepResult_prevoteresp (B := B) c _ _ _ _ _ _ _ _ Hty (.inl Hrole)
          (Hvoter (by rw [Hrole]; decide)) Hnw Hwf Hres
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Herrn with %Herrn
      subst Herrn
      try wp_auto
      iapply HΦ $$ %interface.nil %s1
      iframe Hphys
      ipureintro
      exact ⟨Hwf1, ⟨[], fun _ h => absurd h List.not_mem_nil, Hst⟩, rfl, Hresp, Hft⟩
    · -- Leader: no arm
      simp only [stepFuncOf]
      imod (preceipt_zero (GF := GF)) with #Hrc00
      wp_apply _P.stepLeader c r id s ml m ents sn ctx rs 0
          (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl Hty))))))))
          Hrole
          (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
          (fun Hc => by
            exfalso; rw [Hty] at Hc
            rcases Hc with Hc | ⟨Hc, -⟩ <;> exact absurd Hc (by w32_ne))
          (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
          (fun Hc => by exfalso; rw [Hty] at Hc; rcases Hc with Hc | Hc | Hc <;> exact absurd Hc (by w32_ne))
          (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
          (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
          (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
          (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        $$ [Hphys Hm] as %err %s' %dropped ⟨Hphys, -, %Hres, Herrn⟩
      · iframe Hphys Hrc00
        isplitl [Hm]
        · rw [ite_eq_right Hnp]; iexact Hm
        · iintro %Hc; exfalso; exact Hnp Hc
      obtain ⟨rfl, rfl⟩ := leaderStepResult_prevoteresp c _ _ _ _ _ _ _ Hty Hres
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Herrn with %Herrn
      subst Herrn
      try wp_auto
      iapply HΦ $$ %interface.nil %_
      iframe Hphys
      ipureintro
      exact ⟨Hwf, ⟨[], fun _ h => absurd h List.not_mem_nil, StepCD.frame (.refl _) (RFrame.refl _)⟩, rfl,
      RespStep.refl _ _, keep_frame rfl rfl rfl rfl rfl⟩
    · -- PreCandidate: the pre-vote tally
      simp only [stepFuncOf]
      wp_apply _P.stepCandidate c ∅ r id s ml m ents sn rs (zero_val _) ctx
          (.inr (.inr (.inr (.inr (.inr (.inr (.inl Hty)))))))
          (fun Hc => by
            exfalso; rw [Hty] at Hc
            rcases Hc with Hc | Hc | Hc | Hc <;> exact absurd Hc (by w32_ne))
          (.inr Hrole)
          (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
          (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
          (fun Hp _ => Hnw Hp)
          (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        $$ [Hphys Hm] as %err %s1 %dropped %c1 ⟨Hphys, %Hres, Herrn⟩
      · iframe Hphys; rw [ite_eq_right Hnp]; iexact Hm
      obtain ⟨rfl, rfl, Hwf1, Hst, Hresp, Hft⟩ :=
        candidateStepResult_prevoteresp (B := B) c _ _ _ _ _ _ _ _ Hty (.inr Hrole)
          (Hvoter (by rw [Hrole]; decide)) Hnw Hwf Hres
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Herrn with %Herrn
      subst Herrn
      try wp_auto
      iapply HΦ $$ %interface.nil %s1
      iframe Hphys
      ipureintro
      exact ⟨Hwf1, ⟨[], fun _ h => absurd h List.not_mem_nil, Hst⟩, rfl, Hresp, Hft⟩))

end EtcdGrove
end Perennial
