/-
`value.listUnstructured.AtUsing`: proved (Prove step, notes/smd-plan.md). Its callees' specs (and the interface bundles' laws, `Objects.lean`) are its
hypotheses. Lean-first (2026-11-19), Draft.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__AtUsing
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.heapAllocator__allocValueUnstructured
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.freelistAllocator__allocValueUnstructured
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__reuse
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofs

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

theorem value.listUnstructured.AtUsing.wp_proof
    (h_heapAllocator_allocValueUnstructured : value.heapAllocator.allocValueUnstructured.spec (GF := GF))
    (h_freelistAllocator_allocValueUnstructured : value.freelistAllocator.allocValueUnstructured.spec (GF := GF))
    (h_valueUnstructured_reuse : value.valueUnstructured.reuse.spec (GF := GF)) :
    value.listUnstructured.AtUsing.spec (GF := GF) := fun l vs al n x => by
  wp_start as ⟨Hl, Ha, %Hx⟩
  icases isListV_val $$ Hl with ⟨%xs, #Hs, HL⟩
  ihave ⟨%i, %Hxi, Hi⟩ := isIfaceL_lookup xs vs _ x Hx.2 $$ HL
  ihave %Hsl := ownSlice_len $$ Hs
  have hlt : (BitVec.toInt n).toNat < xs.length := (List.getElem?_eq_some_iff.mp Hxi).1
  have hb : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z l.len := by constructor <;> word
  icases isAlloc_concrete_law_holds al $$ Ha with ⟨Ha, (⟨%p, %rfl⟩ | ⟨%p, %rfl⟩)⟩
  · wp_auto
    simp only [hb, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index l (sint.Z n) xs DFrac.discard i (by word) as -
    · isplitr
      · iexact Hs
      · ipureintro; exact Hxi
    wp_apply h_heapAllocator_allocValueUnstructured p as %q Hq
    wp_apply h_valueUnstructured_reuse q i x $$ [Hq Hi] as %v ⟨%rfl, Hv⟩
    · iframe
    wp_end
  · wp_auto
    simp only [hb, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index l (sint.Z n) xs DFrac.discard i (by word) as -
    · isplitr
      · iexact Hs
      · ipureintro; exact Hxi
    wp_apply h_freelistAllocator_allocValueUnstructured p $$ [Ha] as %q ⟨Ha, Hq⟩
    · iexact Ha
    wp_apply h_valueUnstructured_reuse q i x $$ [Hq Hi] as %v ⟨%rfl, Hv⟩
    · iframe
    wp_end

end proof

end smd
end EtcdGrove
end Perennial
