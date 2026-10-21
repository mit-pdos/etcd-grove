/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgVote_lt.v.

One case of `Step`'s `MsgVote` branch with `m.Term ≤ r.Term`, in its own file so that
it checks in parallel with the others -- see `proof_raft__Step_MsgVote_le.v`
(`MsgVote_le.lean`), which combines them, and `notes/decisions.md` (2026-09-17;
2026-09-18 for why this directory exists). Proof structure, not specification: no
`Module Type`, no `Parameter`; only `MsgVote_le.lean` may import this module.

Lean notes:
* The branch lemma takes the callee specs (Rocq's functor argument `P : STEP_POSTULATES`)
  as its first argument `_P : raft.Step.Postulates`, and Rocq's section variable `c`
  as its second.
* Rocq's `Local Ltac recv_elem` (`∀ m' ∈ recv, m' = a` for the concrete `recv` lists
  `[]`, `[a]`, `[a] ++ [a]`, by rewriting the membership away rather than `set_solver`,
  which took 150s and more there) is not ported.

raft v3.7 (2026-10-15, stage R4 phase 3): the message is a pointer `ml` with `msgIn ml □ ⟨m, ents,
sn, ctx, rs⟩`, read by the getters (`wp_get`/`wp_gets`, `ElectionLemmas.lean`, by `PB`); a response
is a fresh `*pb.Message` sharing the request's `From` (granted: and `Term`) cell
(`msgPtsC_From_acc`/`_Term_acc`, `msgOwn_of_resp`), handed to `send`.
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.raft__Step.ElectionLemmas

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
/-- `MsgVote` with `m.Term < r.Term`: a stale vote request, dropped silently after the
log line. -/
theorem wp_Step_MsgVote_lt (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (PB : raft.Step.PbPostulates (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc) :
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
            StepCD c id B m s recv s'⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ }} := by
  intro Hty Hto Hterm Hfnz Hlt0 Hwf
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
  -- `(r.checkQuorum || r.preVote) && (m.Type == MsgHeartbeat || m.Type == MsgApp)` is false
  -- whichever way the flags go (a `MsgVote` is neither): the condition is joined at `false`
  -- (`wp_join`), so the rest of the arm is verified once, not once per flag case
  wp_join (v := #false) at (If (If _ (Val #true) _) _ (Val #false)) with [Hphys r m Hm]
  · wp_gets
    wp_cq_pv
    -- pre-vote on: not MsgHeartbeat, not MsgApp
    all_goals try
      (wp_gets
       rw [decide_eq_false (show (MsgSt.mk m ents sn ctx rs).msg.Type' ≠ W32 8 by
         show m.Type' ≠ _; rw [Hty]; w32_ne)]
       try wp_auto
       wp_gets
       rw [decide_eq_false (show (MsgSt.mk m ents sn ctx rs).msg.Type' ≠ W32 3 by
         show m.Type' ≠ _; rw [Hty]; w32_ne)]
       try wp_auto)
    all_goals wp_join_done
  -- not a MsgPreVote
  wp_gets
  rw [decide_eq_false (show m.Type' ≠ W32 17 by rw [Hty]; w32_ne)]
  try wp_auto
  -- not a MsgStorageAppendResp either, so the message is just logged
  wp_gets
  rw [decide_eq_false (show m.Type' ≠ W32 20 by rw [Hty]; w32_ne)]
  try wp_auto
  wp_gets
  wp_apply raft.wp_load_idC $$ Hphys as Hphys
  wp_gets
  wp_apply raft.wp_load_TermC $$ Hphys as Hphys
  wp_gets
  wp_raft_logC
  -- nothing was sent and nothing changed: dropping is `StepC.refl`
  iapply HΦ $$ %interface.nil %s
  iframe Hphys
  ipureintro
  exact ⟨Hwf, ⟨[], fun _ H => absurd H List.not_mem_nil, StepCD.frame (stepCF_drop c id _) (RFrame.refl _)⟩, rfl,
    keep_frame rfl rfl rfl rfl rfl⟩

end StepProof

end branches

end EtcdGrove
end Perennial
