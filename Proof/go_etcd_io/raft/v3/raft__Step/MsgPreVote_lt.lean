/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgPreVote_lt.v.

One term case of `Step`'s `MsgPreVote` branch (2026-10-04): the incoming term is
stale. In its own file so that it checks in parallel with the others;
`MsgPreVote.lean` combines them. Proof structure, not specification: no `Module Type`,
no `Parameter`; only files in this directory may import it.

Lean notes:
* The branch lemma takes the callee specs (Rocq's functor argument
  `P : STEP_POSTULATES`) as its first argument `_P : raft.Step.Postulates`, and Rocq's
  section variable `c` as its second.
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

namespace StepProof

/-- `MsgPreVote` with `m.Term < r.Term`: the stale arm answers with a rejecting
`MsgPreVoteResp` at `r.Term` (raft.go:1144-1152), a free message (`StepC.sendFree`);
`r.Term > m.Term`, so it is not `0`. -/
theorem wp_Step_MsgPreVote_lt (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message) :
    m.Type' = MsgPreVote →
    m.To' = id →
    m.Term' ≠ W64 0 →
    m.From' ≠ W64 0 →
    -- from another node (2026-10-10): the answer goes to `m.From`
    m.From' ≠ id →
    -- this file: the incoming term is stale
    uint.Z m.Term' < uint.Z s.term →
    NStateWf s →
    -- pre-vote on (2026-10-10; `raft.Step.spec`)
    s.prevote = true →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜StepCD c id m s [] s'⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ }} := by
  intro Hty Hto Hterm Hfnz Hfid Hlt0 Hwf Hpvon
  have Hn8 : decide (m.Type' = W32 8) = false := decide_eq_false (by rw [Hty]; w32_ne)
  have Hn3 : decide (m.Type' = W32 3) = false := decide_eq_false (by rw [Hty]; w32_ne)
  have Hy17 : decide (m.Type' = W32 17) = true := decide_eq_true Hty
  have Hs0 : s.term ≠ W64 0 := by intro H0; rw [H0] at Hlt0; word
  wp_start as Hphys
  iNamed Hphys
  wp_auto
  wp_apply _P.traceReceiveMessage
  -- `m.Term ≠ 0`, so the first arm of the term preamble is skipped
  rw [decide_eq_false Hterm]
  wp_auto
  wp_apply raft.wp_load_TermC $$ Hphys as Hphys
  rw [decide_eq_false (show ¬ uint.Z s.term < uint.Z m.Term' by omega)]
  wp_auto
  wp_apply raft.wp_load_TermC $$ Hphys as Hphys
  rw [decide_eq_true Hlt0]
  wp_auto
  -- `(checkQuorum || preVote) && (MsgHeartbeat || MsgApp)`: false either way
  wp_apply raft.wp_load_checkQuorumC $$ Hphys as Hphys
  wp_apply raft.wp_load_preVoteC $$ Hphys as Hphys
  cases s.prevote <;> wp_auto
  all_goals try (rw [Hn8]; wp_auto; rw [Hn3]; wp_auto)
  -- `MsgPreVote`: reject at `r.Term`
  all_goals
    rw [Hy17]
    wp_auto
    wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
    icases ownRaftPhysC_log_same c r id _ $$ Hphys with ⟨Hlog, Hback⟩
    wp_apply _P.lastEntryID $$ [$Hlog] as %lastID ⟨Hlog, -⟩
    ihave Hphys := Hback $$ Hlog
    wp_apply raft.wp_load_idC $$ Hphys as Hphys
    wp_apply raft.wp_load_VoteC $$ Hphys as Hphys
    wp_apply raft.wp_load_TermC $$ Hphys as Hphys
    wp_raft_logC
    wp_apply raft.wp_load_TermC $$ Hphys as Hphys
    wp_apply _P.send c r id s _ [] [] _ (Or.inl rfl)
        (Or.inl ⟨.preVoteResp, Or.inr (Or.inr (Or.inr rfl)), mtypeOf_MsgPreVoteResp, Hs0,
          fun Hc => by rcases Hc with Hc | Hc <;> exact absurd Hc (by w32_ne),
          fun h => absurd h Hfid,
          fun Hpf => absurd (Hpvon.symm.trans Hpf) (by decide), rfl⟩)
      $$ [$Hphys]
    · isplitr
      · iapply ownSlice_nil
      isplitr
      · iapply ownSlice_nil
      iapply send_no_snap
      w32_ne
    iintro Hphys
    wp_auto
    iapply HΦ $$ %interface.nil %_
    iframe Hphys
    ipureintro
    refine ⟨nstateWf_sendMsgs _ _ Hwf, StepCD.frame ?_ (by rframe), rfl,
      keep_frame rfl rfl rfl rfl rfl⟩
    rw [toPState_sendMsgs]
    exact .sendFree _ _ (.inr rfl) rfl

end StepProof

end branches

end EtcdGrove
end Perennial
