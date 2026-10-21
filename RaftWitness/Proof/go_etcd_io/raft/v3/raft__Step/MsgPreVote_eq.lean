/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgPreVote_eq.v.

One term case of `Step`'s `MsgPreVote` branch (2026-10-04): the incoming term is the
node's own. In its own file so that it checks in parallel with the others;
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
join carries the message); the answer is a fresh `*pb.Message` sharing the request's `From` cell
(and, granted, its `Term` cell; rejected, fresh `Term`/`Reject` cells): `msgPtsC_From_acc`,
`msgPtsC_Term_acc`, `msgOwn_of_resp`. `prevote_resp_tail` takes which answer it builds.
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.raft__Step.prevote_lemmas
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

set_option maxHeartbeats 4000000 in
/-- `MsgPreVote` with `m.Term = r.Term`: the preamble does nothing, and the vote arm
answers with a `MsgPreVoteResp` -- granted at `m.Term` or rejected at `r.Term`, the same
term -- recording nothing. What `canVote` evaluates to does not matter to the protocol:
either answer is a free message (`StepC.sendFree`). -/
theorem wp_Step_MsgPreVote_eq (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (PB : raft.Step.PbPostulates (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc) :
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
  intro Hty Hto Hterm Hfnz Hfid Heq0 Hwf
  have Hs0 : s.term ≠ W64 0 := Heq0 ▸ Hterm
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
  rw [decide_eq_false (show ¬ uint.Z s.term < uint.Z m.Term' by rw [Heq0]; omega)]
  wp_auto
  wp_gets
  wp_apply raft.wp_load_TermC $$ Hphys as Hphys
  wp_gets
  rw [decide_eq_false (show ¬ uint.Z m.Term' < uint.Z s.term by rw [Heq0]; omega)]
  wp_auto
  -- the type switch: not `MsgHup` / `MsgStorageAppendResp` / `MsgStorageApplyResp`,
  -- but `MsgPreVote`
  wp_gets
  rw [Hty]
  wp_auto
  -- `canVote`, whatever it is; the evaluation is joined
  wp_join (Q := fun v => iprop(⌜∃ b : Bool, v = #b⌝ ∗ ownRaftPhysCV c c.voters r id s ∗
      r_ptr ↦ r ∗ m_ptr ↦ ml ∗
      msgPtsC ml (DFrac.own 1) DFrac.discard (needsCap m) ⟨m, ents, sn, ctx, rs⟩)) at (if: _ then _ else _)
    with [Hphys r m Hm] as ⟨%Hv, Hphys, r, m, Hm⟩
  · repeat (any_goals cv_step)
    all_goals (iframe; ipureintro; exact ⟨_, rfl⟩)
  obtain ⟨cv, rfl⟩ := Hv
  wp_auto
  wp_gets
  wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
  icases ownRaftPhysC_log_same c r id _ $$ Hphys with ⟨Hlog, Hback⟩
  wp_gets
  wp_apply _P.lastEntryID $$ [$Hlog] as %lastID ⟨Hlog, -⟩
  ihave Hphys := Hback $$ Hlog
  -- `canVote && isUpToDate(…)`: the reject arm is reached two ways
  cases cv
  · -- cannot vote: reject at `r.Term`
    try wp_auto
    wp_gets
    prevote_resp_tail false
  try wp_auto
  wp_gets
  wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
  icases ownRaftPhysC_log_same c r id _ $$ Hphys with ⟨Hlog, Hback⟩
  wp_gets
  wp_apply _P.isUpToDate $$ [$Hlog] as %uptodate ⟨Hlog, -⟩
  ihave Hphys := Hback $$ Hlog
  cases uptodate
  · -- behind: reject
    try wp_auto
    prevote_resp_tail false
  -- grant at `m.Term`, recording nothing
  try wp_auto
  prevote_resp_tail true

end StepProof

end branches

end EtcdGrove
end Perennial
