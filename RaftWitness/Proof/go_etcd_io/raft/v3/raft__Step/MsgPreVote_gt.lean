/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgPreVote_gt.v.

One term case of `Step`'s `MsgPreVote` branch (2026-10-04): the incoming term is
higher. In its own file so that it checks in parallel with the others;
`MsgPreVote.lean` combines them. Proof structure, not specification: no `Module Type`,
no `Parameter`; only files in this directory may import it.

Lean notes:
* The branch lemma takes the callee specs (Rocq's functor argument
  `P : STEP_POSTULATES`) as its first argument `_P : raft.Step.Postulates`, and Rocq's
  section variable `c` as its second.
* Rocq's `Local Ltac cv_step` (one step of `canVote`'s evaluation: a field load
  through `raft.wp_load_VoteC`/`wp_load_lead`/`wp_load_Term`, or a `bool_decide`
  decided by case analysis) is the macro `cv_step` (with `wp_if_destruct` for
  the case analysis); `canVote`'s evaluation is joined with `wp_join` (Rocq:
  `wp_bind` + `wp_wand`). The answer's tail, written out three times in Rocq, is the
  macro `prevote_resp_tail` (both `ElectionLemmas.lean`).

raft v3.7 (2026-10-15, stage R4 phase 3): the message is a pointer `ml` with `msgIn ml □ ⟨m, ents,
sn, ctx, rs⟩`, read by the getters (`wp_get`/`wp_gets`, `ElectionLemmas.lean`, by `PB`; `canVote`'s
join carries the message; `GetContext` for the lease check); the answer is a fresh `*pb.Message` sharing the request's `From` cell
(and, granted, its `Term` cell; rejected, fresh `Term`/`Reject` cells): `msgPtsC_From_acc`,
`msgPtsC_Term_acc`, `msgOwn_of_resp`. `prevote_resp_tail` takes which answer it builds.
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

namespace StepProof

set_option maxHeartbeats 4000000 in
/-- `MsgPreVote` with `m.Term > r.Term`: the lease check passes (2026-10-17: or, with `checkQuorum` on, ignores it),
and a pre-vote **never** steps the node down. `canVote` holds by its third disjunct
(`MsgPreVote` for a future term). The answer is a `MsgPreVoteResp`: granted at `m.Term`
if the candidate's log is up to date, else rejected at `r.Term`; nothing is recorded
either way. Both are free messages: `StepC.sendFree`. The rejection's `Term` is the
node's own, which `send` needs non-zero: at term `0` the candidate is up to date (the
premise `Hutd0`). -/
theorem wp_Step_MsgPreVote_gt (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (PB : raft.Step.PbPostulates (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc) :
    m.Type' = MsgPreVote →
    m.To' = id →
    m.Term' ≠ W64 0 →
    m.From' ≠ W64 0 →
    -- from another node (2026-10-10): the answer goes to `m.From`
    m.From' ≠ id →
    -- this file: the incoming term is strictly higher
    uint.Z s.term < uint.Z m.Term' →
    NStateWf s →
    (s.term = W64 0 →
      plogUpToDate s.logst.prev (s.logst.sents ++ s.logst.uents)
        (entryID.mk m.LogTerm' m.Index') = true) →
    -- (2026-10-17) the requested term within the ceiling (`NGhost.tc`): a grant answers at it
    uint.Z m.Term' ≤ uint.Z s.gh.tc →
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
  intro Hty Hto Hterm Hfnz Hfid Hgt0 Hwf Hutd0 Hptc
  have Hn5 : decide (m.Type' = W32 5) = false := decide_eq_false (by rw [Hty]; w32_ne)
  have Hy17 : decide (m.Type' = W32 17) = true := decide_eq_true Hty
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
  rw [decide_eq_true Hgt0]
  wp_auto
  -- `MsgVote || MsgPreVote`: the lease check
  try (wp_gets; rw [Hn5]; wp_auto)
  wp_gets
  rw [Hy17]
  wp_auto
  -- the lease check (2026-10-17: `inLease` needs `checkQuorum`)
  wp_gets
  wp_apply PB.GetContext.1 $$ [$Hm] as %cs ⟨#Hctx_sl, Hm⟩
  wp_apply wp_string_to_bytes as %ct_sl ⟨ct_sl, -⟩
  wp_apply bytes.wp_Equal _ _ DFrac.discard (DFrac.own 1) ctx (go!"CampaignTransfer")
      $$ [$Hctx_sl $ct_sl] as ⟨-, -⟩
  wp_gets
  -- `force` (2026-10-13): a leader transfer's vote request or not; (2026-10-17) with
  -- `checkQuorum` on, a request within the lease that is not forced is ignored
  wp_lease_check ctx
  all_goals
    -- the step-down switch: `MsgPreVote`, so nothing
    wp_gets
    rw [Hy17]
    wp_auto
    -- the type switch: not `MsgHup` / `MsgStorageAppendResp` / `MsgStorageApplyResp`,
    -- but `MsgPreVote`
    wp_gets
    rw [Hty]
    wp_auto
    -- `canVote`: true by its third disjunct, whichever way the first two go; the
    -- evaluation is joined
    wp_join (Q := fun v => iprop(⌜v = #true⌝ ∗ ownRaftPhysCV c c.voters r id s ∗
        r_ptr ↦ r ∗ m_ptr ↦ ml ∗
        msgPtsC ml (DFrac.own 1) DFrac.discard (needsCap m) ⟨m, ents, sn, ctx, rs⟩))
        at (if: _ then _ else _) with [Hphys r m Hm] as ⟨%Hv, Hphys, r, m, Hm⟩
    · repeat (any_goals cv_step)
      all_goals first | wp_join_done | (exfalso; omega) | (exfalso; exact Hif Hty)
    subst Hv
    try wp_auto
    -- `lastEntryID`, then `isUpToDate`
    wp_gets
    wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
    icases ownRaftPhysC_log_same c r id _ $$ Hphys with ⟨Hlog, Hback⟩
    wp_gets
    wp_apply _P.lastEntryID $$ [$Hlog] as %lastID ⟨Hlog, -⟩
    ihave Hphys := Hback $$ Hlog
    wp_gets
    wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
    icases ownRaftPhysC_log_same c r id _ $$ Hphys with ⟨Hlog, Hback⟩
    wp_gets
    wp_apply _P.isUpToDate $$ [$Hlog] as %uptodate ⟨Hlog, %Hutd⟩
    ihave Hphys := Hback $$ Hlog
    cases uptodate
    · -- behind: reject at `r.Term`, which is not `0`
      simp only at Hutd
      have Hs0 : s.term ≠ W64 0 := fun H0 => by
        have := Hutd0 H0
        rw [← Hutd] at this
        exact Bool.false_ne_true this
      try wp_auto
      prevote_resp_tail false
    -- up to date: grant at `m.Term`, recording nothing
    try wp_auto
    prevote_resp_tail true

end StepProof

end branches

end EtcdGrove
end Perennial
