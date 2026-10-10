/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgStorageAppendResp.v
(857d09190).

`Step`'s `MsgStorageAppendResp` branch (2026-10-05), in its own file. Proof structure,
not specification: no `Module Type`, no `Parameter`; only `Proof/raft__Step.lean` may
import this module.

Lean notes: the branch lemma takes the callee specs (Rocq's functor argument
`P : STEP_POSTULATES`) as its first argument `_P : raft.Step.Postulates`, and Rocq's
section variable `cfg` as its second.
-/
module

public import Proof.go_etcd_io.raft.v3.raft__Step.Base

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

The log is re-split (`logStableTo`) and the protocol sees nothing: `Step.refl`. -/
theorem wp_Step_MsgStorageAppendResp (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message) :
    m.Type' = MsgStorageAppendResp →
    m.Snapshot' = null →
    uint.Z m.Term' ≤ uint.Z s.term →
    (m.Term' = W64 0 ∨ m.Term' = s.term →
     m.Index' ≠ W64 0 →
     StableOk s.logst (entryID.mk m.LogTerm' m.Index')) →
    NStateWf s →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhys cfg r id s }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhys cfg r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hframe" ∷ ⌜LocalFrame s s' ∧ s'.logst.applying = s.logst.applying⌝ ∗
        "%Hrefines" ∷ ⌜Step cfg id (toPState s) [] (toPState s')⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ }} := by
  intro Hty Hsn Hle Hstok Hwf
  wp_start as Hphys
  iNamed Hphys
  wp_auto
  wp_apply _P.traceReceiveMessage
  by_cases Hstale : m.Term' ≠ W64 0 ∧ uint.Z m.Term' < uint.Z s.term
  · -- stale: logged and dropped
    obtain ⟨Hnz, Hlt⟩ := Hstale
    rw [decide_eq_false Hnz]
    wp_auto
    wp_apply raft.wp_load_Term $$ Hphys as Hphys
    rw [decide_eq_false (show ¬ uint.Z s.term < uint.Z m.Term' by omega)]
    wp_auto
    wp_apply raft.wp_load_Term $$ Hphys as Hphys
    rw [decide_eq_true Hlt]
    wp_auto
    wp_apply raft.wp_load_checkQuorum $$ Hphys as Hphys
    wp_apply raft.wp_load_preVote $$ Hphys as Hphys
    -- not `MsgHeartbeat`/`MsgApp`, not `MsgPreVote`: the `MsgStorageAppendResp` arm
    cases s.prevote <;> wp_auto <;> repeat (rw [Hty]; wp_auto)
    all_goals
      by_cases Hi0 : m.Index' = W64 0
      all_goals first
        | (rw [decide_eq_true Hi0]
           wp_auto)
        | (rw [decide_eq_false Hi0]
           wp_auto
           -- the log line
           wp_apply raft.wp_load_id $$ Hphys as Hphys
           wp_apply raft.wp_load_Term $$ Hphys as Hphys
           wp_raft_log)
    -- no snapshot
    all_goals
      rw [decide_eq_true Hsn]
      wp_auto
      iapply HΦ $$ %interface.nil %s
      iframe Hphys
      ipureintro
      exact ⟨Hwf, ⟨⟨rfl, Int.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩, .refl _, rfl⟩
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
       wp_apply raft.wp_load_Term $$ Hphys as Hphys
       rw [decide_eq_false (show ¬ uint.Z s.term < uint.Z m.Term' by rw [Heq]; omega)]
       wp_auto
       wp_apply raft.wp_load_Term $$ Hphys as Hphys
       rw [decide_eq_false (show ¬ uint.Z m.Term' < uint.Z s.term by rw [Heq]; omega)]
       wp_auto)
  -- the type switch: `MsgStorageAppendResp`
  all_goals
    repeat (rw [Hty]; wp_auto)
    by_cases Hi0 : m.Index' = W64 0
    · rw [decide_eq_true Hi0]
      wp_auto
      rw [decide_eq_true Hsn]
      wp_auto
      iapply HΦ $$ %interface.nil %s
      iframe Hphys
      ipureintro
      exact ⟨Hwf, ⟨⟨rfl, Int.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩, .refl _, rfl⟩
    · rw [decide_eq_false Hi0]
      wp_auto
      -- `r.raftLog.stableTo(entryID{m.LogTerm, m.Index})`
      wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
      icases ownRaftPhys_log_at cfg r id s $$ Hphys with ⟨Hlog, Hback⟩
      wp_apply _P.stableTo _ _ _ (Hstok Hmt Hi0) $$ [$Hlog] as Hlog
      ihave Hphys := Hback $$ %_ Hlog
      rw [decide_eq_true Hsn]
      wp_auto
      iapply HΦ $$ %interface.nil %_
      iframe Hphys
      ipureintro
      obtain ⟨Hap, Hun, Hsn', Hip, Hpv, Hst⟩ :=
        logStableTo_fields s.logst (entryID.mk m.LogTerm' m.Index')
      refine ⟨Hwf, ⟨⟨rfl, Hip, Hun, Hsn', Hpv, Hst, logStableTo_storage _ _, rfl⟩, Hap⟩, ?_, rfl⟩
      rw [toPState_logStableTo]
      exact .refl _

end StepProof

end branches

end EtcdGrove
end Perennial
