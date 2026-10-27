/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgPreVote_lt.v.

One term case of `Step`'s `MsgPreVote` branch (2026-10-04): the incoming term is
stale. In its own file so that it checks in parallel with the others;
`MsgPreVote.lean` combines them. Proof structure, not specification: no `Module Type`,
no `Parameter`; only files in this directory may import it.

Lean notes:
* The branch lemma takes the callee specs (Rocq's functor argument
  `P : STEP_POSTULATES`) as its first argument `_P : raft.Step.Postulates`, and Rocq's
  section variable `c` as its second.

raft v3.7 (2026-10-15, stage R4 phase 3): the message is a pointer `ml` with `msgIn ml □ ⟨m, ents,
sn, ctx, rs⟩`, read by the getters (`wp_gets`, `ElectionLemmas.lean`, by `PB`); the rejection is a
fresh `*pb.Message` sharing the request's `From` cell (`msgPtsC_From_acc`, `msgOwn_of_resp`).
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

namespace StepProof

set_option maxHeartbeats 2000000 in
/-- `MsgPreVote` with `m.Term < r.Term`: the stale arm answers with a rejecting
`MsgPreVoteResp` at `r.Term` (raft.go:1144-1152), a free message (`StepC.sendFree`);
`r.Term > m.Term`, so it is not `0`. -/
theorem wp_Step_MsgPreVote_lt (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (PB : raft.Step.PbPostulates (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc) :
    m.Type' = MsgPreVote →
    m.To' = id →
    m.Term' ≠ W64 0 →
    m.From' ≠ W64 0 →
    -- from another node (2026-10-10): the answer goes to `m.From`
    m.From' ≠ id →
    -- this file: the incoming term is stale
    uint.Z m.Term' < uint.Z s.term →
    NStateWf s →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
        -- (stage R4) the message, as `Step` received it
        "Hm" ∷ msgIn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜StepCD c id B m s [] s'⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ }} := by
  intro Hty Hto Hterm Hfnz Hfid Hlt0 Hwf
  have Hn8 : decide (m.Type' = W32 8) = false := decide_eq_false (by rw [Hty]; w32_ne)
  have Hn3 : decide (m.Type' = W32 3) = false := decide_eq_false (by rw [Hty]; w32_ne)
  have Hy17 : decide (m.Type' = W32 17) = true := decide_eq_true Hty
  have Hs0 : s.term ≠ W64 0 := by intro H0; rw [H0] at Hlt0; word
  -- `MessageType.Enum()`'s receiver: `int32` is not an interface (as in `toConfChangeSingle`)
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  wp_start as ⟨Hphys, Hm⟩
  icases msgPtsC_nn _ _ _ _ _ $$ Hm with ⟨%Hnn, Hm⟩
  wp_auto
  wp_gets
  rw [decide_eq_false Hnn]
  wp_auto
  wp_gets
  wp_apply _P.traceReceiveMessage
  try wp_auto
  -- `m.Term ≠ 0`, so the first arm of the term preamble is skipped
  wp_gets
  rw [decide_eq_false Hterm]
  wp_auto
  wp_gets
  wp_apply raft.wp_load_TermC $$ Hphys as Hphys
  wp_gets
  rw [decide_eq_false (show ¬ uint.Z s.term < uint.Z m.Term' by omega)]
  wp_auto
  wp_gets
  wp_apply raft.wp_load_TermC $$ Hphys as Hphys
  wp_gets
  rw [decide_eq_true Hlt0]
  wp_auto
  -- `(checkQuorum || preVote) && (MsgHeartbeat || MsgApp)`: false either way, so joined
  -- (`wp_join`) at `#false`, the flags split (`wp_cq_pv`) in the condition only, and the
  -- rest verified once
  wp_gets
  wp_join (v := #false) at (if: _ then _ else #false) with [Hphys r m Hm]
  · wp_cq_pv
    all_goals try (wp_gets; rw [Hn8]; wp_auto; wp_gets; rw [Hn3]; try wp_auto)
    all_goals wp_join_done
  -- `MsgPreVote`: reject at `r.Term`
  wp_gets
  rw [Hy17]
  wp_auto
  wp_gets
  wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
  icases ownRaftPhysC_log_same c r id _ $$ Hphys with ⟨Hlog, Hback⟩
  wp_gets
  wp_apply _P.lastEntryID $$ [$Hlog] as %lastID ⟨Hlog, -⟩
  ihave Hphys := Hback $$ Hlog
  wp_gets
  wp_apply raft.wp_load_idC $$ Hphys as Hphys
  wp_gets
  wp_apply raft.wp_load_VoteC $$ Hphys as Hphys
  wp_gets
  wp_apply raft.wp_load_TermC $$ Hphys as Hphys
  wp_gets
  wp_raft_logC
  icases msgPtsC_From_acc _ _ _ _ _ $$ Hm with ⟨%pfr, HFr, #cFr, HmB⟩
  wp_load
  ihave Hm := HmB $$ HFr
  try wp_auto
  wp_gets
  wp_apply raft.wp_load_TermC $$ Hphys as Hphys
  try wp_auto
  rw [show raftpb.MsgPreVoteResp = #MsgPreVoteResp from rfl]
  wp_apply PB.Enum MsgPreVoteResp
  iintro %pty Hpty
  wp_auto
  -- the response `&pb.Message{To: m.From, Term: new(r.Term), Type: .., Reject: new(true)}`
  imod cellRO_alloc _ _ $$ Hpty with #cTy
  imod cellRO_alloc _ _ $$ «$v1» with #cTe
  imod cellRO_alloc _ _ $$ «$v3» with #cRj
  imod msgOwn_of_resp _ _ _ _ _ MsgPreVoteResp m.From' s.term true ⊤ $$ [«$a0»] with Hresp
  · iframe «$a0» cTy cFr cTe cRj
  let resp : MessageM :=
    ⟨MsgPreVoteResp, m.From', W64 0, s.term, W64 0, W64 0, W64 0, W64 0, true, W64 0⟩
  wp_gets
  have Hok : SendOk id s resp [] [] [absMsgFrom .preVoteResp resp id resp.Term' [] []] :=
      (Or.inl ⟨.preVoteResp, Or.inr (Or.inr (Or.inr rfl)), mtypeOf_MsgPreVoteResp, Hs0,
        fun Hc => by
          change MsgPreVoteResp = _ ∨ MsgPreVoteResp = _ at Hc
          rcases Hc with Hc | Hc <;> exact absurd Hc (by w32_ne),
        fun h => absurd h Hfid,
        .inl (Int.le_refl _), rfl⟩)
  wp_apply _P.send c r id s «$a0_ptr» resp [] none [] [] _ (Or.inl rfl) Hok
      (fun h => absurd h (by show MsgPreVoteResp ≠ MsgSnap; w32_ne))
      (fun h => absurd h (by show MsgPreVoteResp ≠ MsgApp; w32_ne))
    rfl $$ [$Hphys $Hresp]
  · iapply tsSrc_ne; exact (fun h => absurd h (by show MsgPreVoteResp ≠ MsgSnap; w32_ne))
  iintro Hphys
  wp_auto
  iapply HΦ $$ %interface.nil %_
  iframe Hphys
  ipureintro
  refine ⟨nstateWf_sendMsgs _ _ Hwf, StepCD.frame ?_ (by rframe), rfl,
    keep_frame rfl rfl rfl rfl rfl⟩
  wp_gets
  rw [toPState_sendMsgs]
  exact .sendFree _ _ (.inr rfl) rfl

end StepProof

end branches

end EtcdGrove
end Perennial
