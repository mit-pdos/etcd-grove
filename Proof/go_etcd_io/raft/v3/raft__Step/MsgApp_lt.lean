/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgApp_lt.v.

One term case of `Step`'s `MsgApp` branch (the incoming term is stale: logged and
dropped), in its own file so that it checks in parallel with the others;
`proof_raft__Step_MsgApp.v` combines them. Proof structure, not specification: no
`Module Type`, no `Parameter`; only files in this directory may `Require` it.

Lean notes:
* The branch lemma takes the callee specs (Rocq's functor argument
  `P : STEP_POSTULATES`) as its first argument `_P : raft.Step.Postulates`, and Rocq's
  section variable `cfg` as its second.
* Rocq's `Local Ltac`s `recv_elem` (closing `∀ m' ∈ recv, m' = …` goals: `elem_of_app`,
  `list_elem_of_singleton`, `elem_of_nil`, `naive_solver`) and `wp_load_step` (the load
  of `r.step` in `r.step(r, m)`, bound by hand with `raft.wp_load_step`, as `wp_apply`
  does not find a load in function position) are not ported.
-/
module

public import Proof.go_etcd_io.raft.v3.raft__Step.repl_lemmas

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
variable [AllG GF]

namespace StepProof

theorem wp_Step_MsgApp_lt (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) :
    m.Type' = MsgApp →
    m.To' = id →
    m.Term' ≠ W64 0 →
    m.From' ≠ W64 0 →
    m.From' ≠ id →
    id ∈ cfg →
    NStateWf s →
    -- protocol facts the dispatch derives from the ghost state (`app_recv_wf`,
    -- `app_no_conflict_below_commit`)
    PlogWf (entryID.mk m.LogTerm' m.Index') ents →
    uint.Z m.Index' + (ents.length : Int) + 1 < 2^64 →
    (∀ e ∈ ents, e.Type' = EntryNormal) →
    -- (no conflict premise: a stale message never reaches `maybeAppend`)
    -- this file: the incoming term is stale: logged and dropped
    uint.Z m.Term' < uint.Z s.term →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhys cfg r id s ∗
        "#Hents" ∷ m.Entries' ↦*□ ents ∗
        "Hcap" ∷ ownSliceCap raftpb.Entry m.Entries' (DFrac.own 1) }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhys cfg r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absMsg .app m ents) ∧
            Step cfg id (toPState s) recv (toPState s')⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ }} := by
  intro Hty Hto Hterm Hfnz Hfid Hcfg Hwf Hpwf Hnw Hnorm Hlt
  wp_start as Hphys
  iNamed Hphys
  wp_auto
  wp_apply _P.traceReceiveMessage
  rw [decide_eq_false Hterm]
  wp_auto
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  rw [decide_eq_false (show ¬ uint.Z s.term < uint.Z m.Term' by omega)]
  wp_auto
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  rw [decide_eq_true Hlt]
  wp_auto
  -- `(checkQuorum || preVote) && (MsgHeartbeat || MsgApp)`: `checkQuorum` is off; with
  -- pre-vote on, a stale leader message is answered with a bare `MsgAppResp` at the
  -- node's term (2026-10-04)
  wp_apply raft.wp_load_checkQuorum $$ Hphys as Hphys
  wp_apply raft.wp_load_preVote $$ Hphys as Hphys
  cases Hpv : s.prevote
  · -- not MsgPreVote, not MsgStorageAppendResp: only the log line
    wp_auto
    repeat (rw [Hty]; wp_auto)
    wp_apply raft.wp_load_id $$ Hphys as Hphys
    wp_apply raft.wp_load_Term $$ Hphys as Hphys
    wp_raft_log
    iapply HΦ $$ %interface.nil %s
    iframe Hphys
    ipureintro
    exact ⟨Hwf, ⟨[], fun _ h => absurd h List.not_mem_nil, .refl _⟩, rfl,
      keep_frame rfl rfl rfl rfl rfl⟩
  · wp_auto
    repeat (rw [Hty]; wp_auto)
    let ack : raftpb.Message :=
      { Type' := W32 4, To' := m.From', From' := 0, Term' := 0, LogTerm' := 0, Index' := 0,
        Entries' := slice.nil, Commit' := 0, Vote' := 0, Snapshot' := null, Reject' := false,
        RejectHint' := 0, Context' := slice.nil, Responses' := slice.nil }
    have Hok : SendOk id s ack [] [absMsgFrom .appResp ack id s.term []] :=
      Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))
    wp_apply _P.send cfg r id s ack [] _ (Or.inl rfl) Hok $$ [$Hphys] as Hphys
    · isplitr
      · iapply ownSlice_nil
      · iapply send_no_snap
        exact (by decide : W32 4 ≠ W32 7)
    iapply HΦ $$ %interface.nil %_
    iframe Hphys
    ipureintro
    refine ⟨nstateWf_sendMsgs _ _ Hwf, ⟨[], fun _ h => absurd h List.not_mem_nil, ?_⟩, rfl,
      keep_frame rfl rfl rfl rfl rfl⟩
    exact .zeroAck _ _

end StepProof

end branches

end EtcdGrove
end Perennial
