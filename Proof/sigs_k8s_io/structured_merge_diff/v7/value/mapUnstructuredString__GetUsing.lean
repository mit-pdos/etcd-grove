/-
`value.mapUnstructuredString.GetUsing`: proved (Prove step, notes/smd-plan.md). Its callees' specs (and the interface bundles' laws, `Objects.lean`) are its
hypotheses. Lean-first (2026-11-19), Draft.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__GetUsing
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

theorem value.mapUnstructuredString.GetUsing.wp_proof
    (h_heapAllocator_allocValueUnstructured : value.heapAllocator.allocValueUnstructured.spec (GF := GF))
    (h_freelistAllocator_allocValueUnstructured : value.freelistAllocator.allocValueUnstructured.spec (GF := GF))
    (h_valueUnstructured_reuse : value.valueUnstructured.reuse.spec (GF := GF)) :
    value.mapUnstructuredString.GetUsing.spec (GF := GF) := fun m kvs al k => by
  wp_start as ⟨Hm, Ha⟩
  ihave Hi := isMapV_val $$ Hm
  icases isIface_map_val $$ Hi with ⟨%M, #HM, %Hk, HL⟩
  wp_auto
  wp_apply wp_map_lookup2 go.string (go.InterfaceType []) m M k DFrac.discard as -
  · iexact HM
  cases hl : lookupKV k kvs with
  | none =>
    have hM : M !! k = none := by
      have := Hk.2 k; rw [hl] at this; simpa using this
    simp only [hM]
    wp_auto
    iapply HΦ
    iframe
    simp only [optValF]
    ipureintro
    simp
  | some x =>
    ihave ⟨%i, %Hmi, Hx⟩ := isIfaceM_lookup M k x kvs hl $$ HL
    simp only [Hmi, Option.isSome_some, Option.getD_some]
    wp_auto
    icases isAlloc_concrete_law_holds al $$ Ha with ⟨Ha, (⟨%p, %rfl⟩ | ⟨%p, %rfl⟩)⟩
    · wp_auto
      wp_apply h_heapAllocator_allocValueUnstructured p as %q Hq
      wp_apply h_valueUnstructured_reuse q i x $$ [Hq Hx] as %v ⟨%rfl, Hv⟩
      · iframe
      iapply HΦ
      iframe
      isplitr
      · ipureintro; rfl
      · simp only [optValF]; iexact Hv
    · wp_auto
      wp_apply h_freelistAllocator_allocValueUnstructured p $$ [Ha] as %q ⟨Ha, Hq⟩
      · iexact Ha
      wp_apply h_valueUnstructured_reuse q i x $$ [Hq Hx] as %v ⟨%rfl, Hv⟩
      · iframe
      iapply HΦ
      iframe
      isplitr
      · ipureintro; rfl
      · simp only [optValF]; iexact Hv

end proof

end smd
end EtcdGrove
end Perennial
