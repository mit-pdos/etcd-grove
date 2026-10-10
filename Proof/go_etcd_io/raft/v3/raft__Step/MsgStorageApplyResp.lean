/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgStorageApplyResp.v
(857d09190).

`Step`'s `MsgStorageApplyResp` branch (2026-10-05), in its own file. Proof structure,
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

/-- The local acknowledgement `RawNode.Advance` steps after the application applied a
`Ready`'s committed entries (`newStorageApplyRespMsg`: `Term = 0`, `Entries` the
entries). The term preamble is skipped; the type switch's `MsgStorageApplyResp` case
runs

    if len(m.Entries) > 0 {
        index := m.Entries[len(m.Entries)-1].Index
        r.appliedTo(index, entsSize(m.Entries))
        r.reduceUncommittedSize(payloadsSize(m.Entries))
    }

moving `applied` (`logAppliedTo`). Nothing the protocol sees changes: `Step.refl`. The
premise is `appliedTo`'s: the last entry is committed. -/
theorem wp_Step_MsgStorageApplyResp (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) :
    m.Type' = MsgStorageApplyResp →
    m.Term' = W64 0 →
    (∀ e, ents.getLast? = some e → uint.Z e.Index' ≤ uint.Z s.logst.committed) →
    NStateWf s →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhys cfg r id s ∗
        "#Hents" ∷ m.Entries' ↦*□ ents }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhys cfg r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hframe" ∷ ⌜LocalFrame s s' ∧
                     ((∀ e, ents.getLast? = some e → uint.Z e.Index' ≤ uint.Z s.logst.applying) →
                      s'.logst.applying = s.logst.applying)⌝ ∗
        "%Hrefines" ∷ ⌜Step cfg id (toPState s) [] (toPState s')⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ }} := by
  intro Hty Hterm Hlast Hwf
  wp_start as ⟨Hphys, #Hents⟩
  wp_auto
  wp_apply _P.traceReceiveMessage
  -- `m.Term = 0` (a local message), so the term preamble is skipped
  rw [decide_eq_true Hterm]
  wp_auto
  -- the type switch: not `MsgHup`, not `MsgStorageAppendResp`, but
  -- `MsgStorageApplyResp`
  rw [Hty]
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hents
  cases He : ents.getLast? with
  | none =>
    -- no entries: nothing to do
    rw [List.getLast?_eq_none_iff] at He
    subst He
    rw [decide_eq_false (by simp only [List.length_nil] at Hlen; word)]
    wp_auto
    iapply HΦ $$ %interface.nil %s
    iframe Hphys
    ipureintro
    exact ⟨Hwf, ⟨⟨rfl, Int.le_refl _, rfl, rfl, rfl, rfl⟩, fun _ => rfl⟩, .refl _, rfl⟩
  | some e =>
    obtain ⟨es, rfl⟩ := List.getLast?_eq_some_iff.1 He
    simp only [List.length_append, List.length_singleton] at Hlen
    rw [decide_eq_true (by word)]
    wp_auto
    -- `m.Entries[len(m.Entries)-1].Index`
    rw [ite_eq_left ⟨by word, by word⟩]
    icases ownSlice_elem_acc (sint.Z (m.Entries'.len - W64 1)) e _ _ _ (by word)
      (by rw [show (sint.Z (m.Entries'.len - W64 1)).toNat = es.length by word]; simp)
      $$ Hents with ⟨#He, -⟩
    iStructNamed He
    wp_auto
    wp_apply _P.entsSize $$ [$Hents] as %sz -
    -- `applied ≤ applying`: `applying` stays put when the entries end at or below it
    icases ownRaftPhys_log_same cfg r id s $$ Hphys with ⟨Hlog, Hback⟩
    icases ownRaftLog_ready_wf _ _ $$ Hlog with ⟨%Hrw, Hlog⟩
    ihave Hphys := Hback $$ Hlog
    wp_apply _P.appliedTo cfg r id s e.Index' sz (Hlast e He) $$ [$Hphys] as Hphys
    wp_apply _P.payloadsSize $$ [$Hents] as %psz -
    wp_apply _P.reduceUncommittedSize $$ [$Hphys] as Hphys
    iapply HΦ $$ %interface.nil %_
    iframe Hphys
    ipureintro
    refine ⟨Hwf, ⟨⟨rfl, Int.le_refl _, rfl, rfl, rfl, rfl⟩, fun Hle => ?_⟩, ?_, rfl⟩
    · have H1 := Hle e (by simp)
      show w64Max s.logst.applying (w64Max e.Index' s.logst.applied) = s.logst.applying
      unfold w64Max
      split <;> split <;> word
    rw [toPState_logAppliedTo]
    exact .refl _

end StepProof

end branches

end EtcdGrove
end Perennial
