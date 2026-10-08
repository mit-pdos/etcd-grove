/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgVote_lt.v.

One case of `Step`'s `MsgVote` branch with `m.Term ≤ r.Term`, in its own file so that
it checks in parallel with the others -- see `proof_raft__Step_MsgVote_le.v`
(`MsgVote_le.lean`), which combines them, and `notes/decisions.md` (2026-09-17;
2026-09-18 for why this directory exists). Proof structure, not specification: no
`Module Type`, no `Parameter`; only `MsgVote_le.lean` may import this module.

Lean notes:
* The branch lemma takes the callee specs (Rocq's functor argument `P : STEP_POSTULATES`)
  as its first argument `_P : raft.Step.Postulates`, and Rocq's section variable `cfg`
  as its second.
* Rocq's `Local Ltac recv_elem` (`∀ m' ∈ recv, m' = a` for the concrete `recv` lists
  `[]`, `[a]`, `[a] ++ [a]`, by rewriting the membership away rather than `set_solver`,
  which took 150s and more there) is not ported.
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

/-- `MsgVote` with `m.Term < r.Term`: a stale vote request, dropped silently after the
log line. -/
theorem wp_Step_MsgVote_lt (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) :
    m.Type' = MsgVote →
    m.To' = id →
    m.Term' ≠ W64 0 →
    -- `send` stamps the sender's id into `From`, and node ids are nonzero
    m.From' ≠ W64 0 →
    -- this file: the incoming term is stale, so the message is dropped
    uint.Z m.Term' < uint.Z s.term →
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
  intro Hty Hto Hterm Hfnz Hlt0 Hwf
  wp_start as ⟨Hphys, #Hctx⟩
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
  -- `checkQuorum` is off; with pre-vote on the type test runs: not MsgHeartbeat, not MsgApp
  wp_apply raft.wp_load_checkQuorum $$ Hphys as Hphys
  wp_pures; wp_load; wp_pures
  wp_apply raft.wp_load_preVote $$ Hphys as Hphys
  cases s.prevote
  all_goals (wp_pures; wp_load; wp_pures)
  -- pre-vote on: not MsgHeartbeat, not MsgApp
  all_goals try
    (rw [decide_eq_false (show m.Type' ≠ W32 8 by rw [Hty]; w32_ne)]
     wp_pures; wp_load; wp_pures
     rw [decide_eq_false (show m.Type' ≠ W32 3 by rw [Hty]; w32_ne)]
     (wp_pures; wp_load; wp_pures))
  -- not a MsgPreVote
  all_goals rw [decide_eq_false (show m.Type' ≠ W32 17 by rw [Hty]; w32_ne)]
  all_goals (wp_pures; wp_load; wp_pures)
  -- not a MsgStorageAppendResp either, so the message is just logged
  all_goals rw [decide_eq_false (show m.Type' ≠ W32 20 by rw [Hty]; w32_ne)]
  all_goals (wp_pures; wp_load; wp_pures)
  all_goals
    wp_apply raft.wp_load_id $$ Hphys as Hphys
    wp_pures; wp_load; wp_pures
    wp_apply raft.wp_load_Term $$ Hphys as Hphys
    wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures
    -- TODO(no-wp-auto): macro `wp_raft_log` runs wp_auto: wp_pures | wp_pures; wp_load; wp_pures | wp_pures | wp_pures; iclear r m | ∅ | wp_pures | wp_pures; wp_load; wp_pures | wp_pures | wp_pures; iclear r m | ∅
    wp_raft_log
    -- nothing was sent and nothing changed: dropping is `Step.refl`
    iapply HΦ $$ %interface.nil %s
    iframe Hphys
    ipureintro
    exact ⟨Hwf, ⟨[], fun _ H => absurd H List.not_mem_nil, step_drop cfg id _⟩, rfl⟩

end StepProof

end branches

end EtcdGrove
end Perennial
