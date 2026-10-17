/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgApp_lt.v.

One term case of `Step`'s `MsgApp` branch (the incoming term is stale: logged and
dropped), in its own file so that it checks in parallel with the others;
`proof_raft__Step_MsgApp.v` combines them. Proof structure, not specification: no
`Module Type`, no `Parameter`; only files in this directory may `Require` it.

Lean notes:
* The branch lemma takes the callee specs (Rocq's functor argument
  `P : STEP_POSTULATES`) as its first argument `_P : raft.Step.Postulates`, and Rocq's
  section variable `c` as its second.
* Rocq's `Local Ltac`s `recv_elem` (closing `∀ m' ∈ recv, m' = …` goals: `elem_of_app`,
  `list_elem_of_singleton`, `elem_of_nil`, `naive_solver`) and `wp_load_step` (the load
  of `r.step` in `r.step(r, m)`, bound by hand with `raft.wp_load_stepC`, as `wp_apply`
  does not find a load in function position) are not ported.
-/
module

public import Proof.go_etcd_io.raft.v3.raft__Step.repl_lemmas
public import Proof.go_etcd_io.raft.v3.raft__Step.ReplLemmas

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

set_option maxHeartbeats 1000000 in
theorem wp_Step_MsgApp_lt (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (_Q : raft.Step.ReplPbPostulates (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc)
    (ents : List EntryM) :
    m.Type' = MsgApp →
    m.To' = id →
    m.Term' ≠ W64 0 →
    m.From' ≠ W64 0 →
    m.From' ≠ id →
    NStateWf s →
    -- protocol facts the dispatch derives from the ghost state (`app_recv_wf`,
    -- `app_no_conflict_below_commit`)
    PlogWf (entryID.mk m.LogTerm' m.Index') ents →
    uint.Z m.Index' + (ents.length : Int) + 1 < 2^64 →
    -- (no conflict premise: a stale message never reaches `maybeAppend`)
    -- this file: the incoming term is stale: logged and dropped
    uint.Z m.Term' < uint.Z s.term →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
        "Hm" ∷ msgIn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absMsg .app m ents) ∧
            StepCD c id m s recv s'⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ }} := by
  intro Hty Hto Hterm Hfnz Hfid Hwf Hpwf Hnw Hlt
  wp_start as H
  iNamed H
  icases msgPtsC_nn _ _ _ _ _ $$ Hm with ⟨%Hnn, Hm⟩
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply _P.traceReceiveMessage
  try wp_auto
  wp_get _Q
  rw [decide_eq_false Hterm]
  wp_auto
  wp_drive _Q
  rw [decide_eq_false (show ¬ uint.Z s.term < uint.Z m.Term' by omega)]
  wp_auto
  wp_drive _Q
  rw [decide_eq_true Hlt]
  wp_auto
  -- `(checkQuorum || preVote) && (MsgHeartbeat || MsgApp)`: `checkQuorum` is off; with
  -- pre-vote on, a stale leader message is answered with a bare `MsgAppResp` at the
  -- node's term (2026-10-04)
  wp_drive _Q
  cases Hpv : s.prevote
  · -- not MsgPreVote, not MsgStorageAppendResp: only the log line
    wp_auto
    wp_drive _Q
    wp_raft_logC
    iapply HΦ $$ %interface.nil %s
    iframe Hphys
    ipureintro
    exact ⟨Hwf, ⟨[], fun _ h => absurd h List.not_mem_nil, StepCD.frame (.refl _) (by rframe)⟩, rfl,
      keep_frame rfl rfl rfl rfl rfl⟩
  · wp_auto
    wp_drive _Q
    icases msgPtsC_From_acc _ _ _ _ _ $$ Hm with ⟨%pfr, HFr, #cFr, Hmback⟩
    wp_auto
    rw [show raftpb.MsgAppResp = #((W32 4 : raftpb.MessageType)) from rfl]
    haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
    wp_apply _Q.Enum (W32 4)
    iintro %pty Hpty
    imod cellRO_alloc $$ Hpty with #cTy
    wp_auto
    iclear Hmback HFr
    let ack : MessageM := ⟨W32 4, m.From', 0, 0, 0, 0, 0, 0, false, 0⟩
    imod msgOwn_of_scalars «$a0_ptr» _ ack ⊤ $$ [«$a0»] with Hack
    · iframe «$a0» cTy cFr
      isplitr; · ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      repeat (isplitr; · iapply cellRO_null)
      iapply cellRO_null
    have Hok : SendOk id s ack [] [] [absMsgFrom .appResp ack id s.term []] :=
      Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, fun h => absurd h Hfid, rfl⟩)))
    wp_apply _P.send c r id s «$a0_ptr» ack [] none [] [] _ (Or.inl rfl) Hok
      (fun h => absurd h (by simp only [ack]; w32_ne)) $$ [$Hphys $Hack] as Hphys
    iapply HΦ $$ %interface.nil %_
    iframe Hphys
    ipureintro
    refine ⟨nstateWf_sendMsgs _ _ Hwf, ⟨[], fun _ h => absurd h List.not_mem_nil, ?_⟩, rfl,
      keep_frame rfl rfl rfl rfl rfl⟩
    refine StepCD.frame ?_ (by rframe)
    exact .zeroAck _ _

end StepProof

end branches

end EtcdGrove
end Perennial
