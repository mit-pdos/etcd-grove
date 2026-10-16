/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgStorageAppendResp.v
(857d09190).

`Step`'s `MsgStorageAppendResp` branch (2026-10-05), in its own file. Proof structure,
not specification: no `Module Type`, no `Parameter`; only `Proof/raft__Step.lean` may
import this module.

Lean notes: the branch lemma takes the callee specs (Rocq's functor argument
`P : STEP_POSTULATES`) as its first argument `_P : raft.Step.Postulates`, and Rocq's
section variable `c` as its second.
-/
module

public import Proof.go_etcd_io.raft.v3.raft__Step.Base
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
/-- The local acknowledgement `RawNode.Advance` steps after the application persisted a
`Ready`'s entries (`newStorageAppendRespMsg`: `Term` the term at `acceptReady`,
`Index`/`LogTerm` the last entry then, no snapshot). By the term:

- `Term = 0` or `Term = r.Term`: the type switch's case runs
  `if m.Index != 0 { r.raftLog.stableTo(entryID{m.LogTerm, m.Index}) }` and finds
  `m.Snapshot` `nil`;
- `Term < r.Term` (the node moved on since the `Ready`): the preamble's stale-message
  arm, which for this type only logs (and would apply a snapshot, `nil` here);
- `Term > r.Term` would make the node step down to a term no message brought --
  excluded by the premise.

The log is re-split (`logStableTo`) and the protocol sees nothing: `StepC.refl`. -/
theorem wp_Step_MsgStorageAppendResp (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (_Q : raft.Step.ReplPbPostulates (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc) (ents : List EntryM) :
    m.Type' = MsgStorageAppendResp →
    sn = none →
    uint.Z m.Term' ≤ uint.Z s.term →
    (m.Term' = W64 0 ∨ m.Term' = s.term →
     m.Index' ≠ W64 0 →
     StableOk s.logst (entryID.mk m.LogTerm' m.Index')) →
    s.gh.unst = false →
    NStateWf s →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
        "Hm" ∷ msgIn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hframe" ∷ ⌜LocalFrame s s' ∧ s'.logst.applying = s.logst.applying⌝ ∗
        "%Hrefines" ∷ ⌜StepCD c id m s [] s'⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ }} := by
  intro Hty Hsn Hle Hstok Hghoff Hwf
  wp_start as H
  iNamed H
  icases msgPtsC_not_null _ _ _ _ _ $$ Hm with ⟨%Hnn, Hm⟩
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply _P.traceReceiveMessage
  try wp_auto
  wp_get _Q
  by_cases Hstale : m.Term' ≠ W64 0 ∧ uint.Z m.Term' < uint.Z s.term
  · -- stale: logged and dropped
    obtain ⟨Hnz, Hlt⟩ := Hstale
    rw [decide_eq_false Hnz]
    wp_auto
    wp_drive _Q
    rw [decide_eq_false (show ¬ uint.Z s.term < uint.Z m.Term' by omega)]
    wp_auto
    wp_drive _Q
    rw [decide_eq_true Hlt]
    wp_auto
    wp_drive _Q
    -- not `MsgHeartbeat`/`MsgApp`, not `MsgPreVote`: the `MsgStorageAppendResp` arm
    wp_drive _Q
    cases s.prevote <;> (try wp_auto) <;> wp_drive _Q
    all_goals
      by_cases Hi0 : m.Index' = W64 0
      all_goals first
        | (rw [decide_eq_true Hi0]
           wp_auto)
        | (rw [decide_eq_false Hi0]
           wp_auto
           -- the log line
           wp_drive _Q
           wp_raft_logC)
    -- no snapshot
    all_goals
      wp_apply wp_GetSnapshot_none _Q _ _ _ _ _ Hsn $$ [$Hm] as Hm
      try wp_auto
      iapply HΦ $$ %interface.nil %s
      iframe Hphys
      ipureintro
      exact ⟨Hwf, ⟨⟨rfl, Int.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩,
        StepCD.frame (.refl _) (RFrame.refl _), rfl⟩
  -- `Term = 0` or `Term = r.Term`: the switch's case
  have Hmt : m.Term' = W64 0 ∨ m.Term' = s.term := by
    by_cases Hz : m.Term' = W64 0
    · exact .inl Hz
    · right
      have : ¬ uint.Z m.Term' < uint.Z s.term := fun h => Hstale ⟨Hz, h⟩
      word
  by_cases Hz : m.Term' = W64 0
  all_goals first
    | (rw [decide_eq_true Hz]
       wp_auto)
    | (rw [decide_eq_false Hz]
       wp_auto
       have Heq : m.Term' = s.term := Hmt.resolve_left Hz
       wp_drive _Q
       rw [decide_eq_false (show ¬ uint.Z s.term < uint.Z m.Term' by rw [Heq]; omega)]
       wp_auto
       wp_drive _Q
       rw [decide_eq_false (show ¬ uint.Z m.Term' < uint.Z s.term by rw [Heq]; omega)]
       wp_auto)
  -- the type switch: `MsgStorageAppendResp`
  all_goals
    wp_drive _Q
    by_cases Hi0 : m.Index' = W64 0
    · rw [decide_eq_true Hi0]
      wp_auto
      wp_apply wp_GetSnapshot_none _Q _ _ _ _ _ Hsn $$ [$Hm] as Hm
      try wp_auto
      iapply HΦ $$ %interface.nil %s
      iframe Hphys
      ipureintro
      exact ⟨Hwf, ⟨⟨rfl, Int.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩,
        StepCD.frame (.refl _) (RFrame.refl _), rfl⟩
    · rw [decide_eq_false Hi0]
      wp_auto
      -- `r.raftLog.stableTo(entryID{m.LogTerm, m.Index})`
      wp_drive _Q
      wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
      icases ownRaftPhysC_log_at c r id s $$ Hphys with ⟨Hlog, -, Hback⟩
      wp_apply _P.stableTo _ _ _ (Hstok Hmt Hi0) $$ [$Hlog] as Hlog
      ihave Hphys := Hback $$ %_ Hlog %(LogGhOk.of_off Hghoff)
      wp_apply wp_GetSnapshot_none _Q _ _ _ _ _ Hsn $$ [$Hm] as Hm
      try wp_auto
      iapply HΦ $$ %interface.nil %_
      iframe Hphys
      ipureintro
      obtain ⟨Hap, Hun, Hsn', Hip, Hpv, Hst⟩ :=
        logStableTo_fields s.logst (entryID.mk m.LogTerm' m.Index')
      refine ⟨Hwf, ⟨⟨rfl, Hip, Hun, Hsn', Hpv, Hst, logStableTo_storage _ _, rfl, rfl⟩, Hap⟩, ?_, rfl⟩
      refine StepCD.frame ?_ ⟨by unfold logStableTo; split <;> rfl, Hsn', fun h => ⟨h, rfl⟩⟩
      rw [toPState_logStableTo]
      exact .refl _

end StepProof

end branches

end EtcdGrove
end Perennial
