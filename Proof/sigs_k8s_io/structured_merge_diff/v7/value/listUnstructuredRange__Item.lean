/-
`value.listUnstructuredRange.Item`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Its callees' specs (and the interface bundles' laws, `Objects.lean`) are its
hypotheses. Lean-first (2026-11-19), Draft.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructuredRange__Item
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__reuse
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.value.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.value.Objects

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : value.Assumptions]

theorem value.listUnstructuredRange.Item.wp_proof
    (h_valueUnstructured_reuse : value.valueUnstructured.reuse.spec (GF := GF)) :
    value.listUnstructuredRange.Item.spec (GF := GF) := fun q vs n x => by
  wp_start as ⟨Hr, %Hx⟩
  iunfold ownRange at Hr
  icases Hr with (⟨%q', %h⟩ | ⟨%q', %sl, %w, %iw, %h, Hq, #Hli, Hw⟩)
  · exfalso; simp at h; exact emptyRange_ne_listUnstructuredRange h.1.1.symm
  obtain ⟨hq, rfl⟩ := h
  simp [intoVal_eq_iff] at hq
  subst hq
  ihave #Hl := isListV_intro $$ Hli
  icases isListV_val $$ Hl with ⟨%xs, #Hs, HL⟩
  ihave ⟨%i, %Hxi, Hi⟩ := isIfaceL_lookup xs vs _ x Hx.2 $$ HL
  ihave %Hsl := ownSlice_len $$ Hs
  have hlt : (BitVec.toInt iw).toNat < xs.length := (List.getElem?_eq_some_iff.mp Hxi).1
  wp_auto
  wp_if_destruct
  · exfalso; word
  wp_if_destruct
  · exfalso; word
  have hb : 0 ≤ sint.Z iw ∧ sint.Z iw < sint.Z sl.len := by constructor <;> word
  simp only [hb, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index sl (sint.Z iw) xs DFrac.discard i (by word) as -
  · isplitr
    · iexact Hs
    · ipureintro; exact Hxi
  wp_apply h_valueUnstructured_reuse w i x $$ [Hw Hi] as %v ⟨%rfl, Hv⟩
  · iframe; iexact Hi
  iapply HΦ
  isplitr
  · ipureintro; rfl
  iframe
  iintro Hv
  icases isValF_elim $$ Hv with ⟨%i', Hw, -⟩
  iapply ownRange_intro q sl w iw vs _ rfl
  iframe
  isplitr
  · iexact Hli
  · iunfold wrapperOwn; iexists i'; iexact Hw

end proof

end smd
end EtcdGrove
end Perennial
