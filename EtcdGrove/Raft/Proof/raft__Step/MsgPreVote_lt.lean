/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgPreVote_lt.v.

One term case of `Step`'s `MsgPreVote` branch (2026-10-04): the incoming term is
stale. In its own file so that it checks in parallel with the others;
`MsgPreVote.lean` combines them. Proof structure, not specification: no `Module Type`,
no `Parameter`; only files in this directory may import it.

Lean notes:
* The branch lemma takes the callee specs (Rocq's functor argument
  `P : STEP_POSTULATES`) as its first argument `_P : raft.Step.Postulates`, and Rocq's
  section variable `cfg` as its second.
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

/-- `MsgPreVote` with `m.Term < r.Term`: the stale arm answers with a rejecting
`MsgPreVoteResp` at `r.Term` (raft.go:1144-1152), a free message (`Step.sendFree`);
`r.Term > m.Term`, so it is not `0`. -/
theorem wp_Step_MsgPreVote_lt (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message) :
    m.Type' = MsgPreVote →
    m.To' = id →
    m.Term' ≠ W64 0 →
    m.From' ≠ W64 0 →
    -- this file: the incoming term is stale
    uint.Z m.Term' < uint.Z s.term →
    NStateWf s →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhys cfg r id s }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhys cfg r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜Step cfg id (toPState s) [] (toPState s')⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ }} := by
  intro Hty Hto Hterm Hfnz Hlt0 Hwf
  have Hn8 : decide (m.Type' = W32 8) = false := decide_eq_false (by rw [Hty]; w32_ne)
  have Hn3 : decide (m.Type' = W32 3) = false := decide_eq_false (by rw [Hty]; w32_ne)
  have Hy17 : decide (m.Type' = W32 17) = true := decide_eq_true Hty
  have Hs0 : s.term ≠ W64 0 := by intro H0; rw [H0] at Hlt0; word
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
  rw [decide_eq_false (show ¬ uint.Z s.term < uint.Z m.Term' by omega)]
  wp_pures; wp_load; wp_load; wp_pures
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  wp_pures
  rw [decide_eq_true Hlt0]
  wp_pures; wp_load; wp_pures
  -- `(checkQuorum || preVote) && (MsgHeartbeat || MsgApp)`: false either way
  wp_apply raft.wp_load_checkQuorum $$ Hphys as Hphys
  wp_pures; wp_load; wp_pures
  wp_apply raft.wp_load_preVote $$ Hphys as Hphys
  cases s.prevote <;> (wp_pures; wp_load; wp_pures)
  all_goals try (rw [Hn8]; wp_pures; wp_load; wp_pures; rw [Hn3]; wp_pures; wp_load; wp_pures)
  -- `MsgPreVote`: reject at `r.Term`
  all_goals
    rw [Hy17]
    wp_pures; wp_load; wp_pures
    wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
    wp_pures
    icases ownRaftPhys_log_same cfg r id _ $$ Hphys with ⟨Hlog, Hback⟩
    wp_apply _P.lastEntryID $$ [$Hlog] as %lastID ⟨Hlog, -⟩
    wp_pures; wp_alloc last_ptr as last; wp_pures; wp_store; wp_pures; wp_load; wp_pures
    ihave Hphys := Hback $$ Hlog
    wp_apply raft.wp_load_id $$ Hphys as Hphys
    wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures; iclear last
    wp_apply raft.wp_load_Vote $$ Hphys as Hphys
    wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load
    wp_pures
    wp_apply raft.wp_load_Term $$ Hphys as Hphys
    wp_pures
    wp_raft_log
    wp_pures; wp_load; wp_pures; wp_load; wp_pures
    wp_apply raft.wp_load_Term $$ Hphys as Hphys
    wp_pures; wp_load; wp_pures
    wp_apply _P.send cfg r id s _ [] _ (Or.inl rfl)
        (Or.inl ⟨.preVoteResp, Or.inr (Or.inr (Or.inr rfl)), mtypeOf_MsgPreVoteResp, Hs0,
          fun Hc => by rcases Hc with Hc | Hc <;> exact absurd Hc (by w32_ne), rfl⟩)
      $$ [$Hphys]
    · isplitr
      · iapply ownSlice_nil
      iapply send_no_snap
      w32_ne
    iintro Hphys
    wp_pures; iclear r m
    iapply HΦ $$ %interface.nil %_
    iframe Hphys
    ipureintro
    refine ⟨nstateWf_sendMsgs _ _ Hwf, ?_, rfl⟩
    rw [toPState_sendMsgs]
    exact .sendFree _ _ (.inr rfl) rfl

end StepProof

end branches

end EtcdGrove
end Perennial
