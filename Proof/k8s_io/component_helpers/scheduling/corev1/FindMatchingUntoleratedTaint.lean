/-
Proof of `Spec/k8s_io/component_helpers/scheduling/corev1/FindMatchingUntoleratedTaint.lean`.
Lean-first.
-/
module

public import Spec.k8s_io.component_helpers.scheduling.corev1.FindMatchingUntoleratedTaint
public import Spec.k8s_io.component_helpers.scheduling.corev1.getFilteredTaints
public import Spec.k8s_io.component_helpers.scheduling.corev1.TolerationsTolerateTaint

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.component_helpers.scheduling.corev1.Assumptions]

theorem FindMatchingUntoleratedTaint.wp_proof
    (wp_getFilteredTaints : getFilteredTaints.spec (GF := GF) (hG := hG))
    (wp_TolerationsTolerateTaint : TolerationsTolerateTaint.spec (GF := GF) (hG := hG)) :
    FindMatchingUntoleratedTaint.spec (GF := GF) (hG := hG) := by
  intro logger ns dq nvs ts dq' tols f P en
  wp_start as ⟨Hns, Hts, #Hf⟩
  wp_auto
  wp_apply (wp_getFilteredTaints ns dq nvs f P) $$ [$Hns $Hf] as %fs ⟨Hns, Hfs⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hfs
  ihave HI : (∃ (j : w64), "i" ∷ i_ptr ↦ j ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z fs.len ∧ (tols = [] → j = W64 0)⌝ ∗
      "Hfs" ∷ fs ↦* nvs.filter P ∗ "Hts" ∷ ts ↦*{dq'} tols ∗ "Hns" ∷ ns ↦*{dq} nvs ∗
      "enableComparisonOperators" ∷ enableComparisonOperators_ptr ↦ en ∗
      "tolerations" ∷ tolerations_ptr ↦ ts ∗ "logger" ∷ logger_ptr ↦ logger : IProp GF)
    $$ [-HΦ]
  · iexists W64 0
    iframe
    ipureintro; exact ⟨by word, by word, fun _ => rfl⟩
  wp_for HI
  by_cases hlt : sint.Z j < sint.Z fs.len
  · simp only [hlt, _root_.decide_true, ↓reduceIte]
    wp_auto
    obtain ⟨v, hv⟩ : ∃ v, (nvs.filter P)[sint.nat j]? = some v :=
      ⟨_, List.getElem?_eq_getElem (by word)⟩
    have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z fs.len := ⟨Hj.1, hlt⟩
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply (wp_load_slice_index fs (sint.Z j) (nvs.filter P) _ v Hj.1) $$ [Hfs] as Hfs
    · iframe; ipureintro; simpa [sint.nat] using hv
    wp_apply (wp_TolerationsTolerateTaint logger ts dq' tols taint_ptr (DFrac.own 1) v en)
      $$ [$Hts $taint] as %b ⟨Hts, taint, %Hb⟩
    cases b
    · wp_auto
      wp_for_post
      iapply HΦ
      iframe
      ipureintro
      have hmem : v ∈ nvs.filter P := List.mem_of_getElem? hv
      refine ⟨fun h => by rw [h] at hmem; simp at hmem, fun _ => ?_, fun _ => hmem⟩
      cases h : nvs.filter P with
      | nil => rw [h] at hmem; simp at hmem
      | cons _ _ => rfl
    · wp_auto
      wp_for_post
      iframe
      iexists j + W64 1
      iframe
      ipureintro
      refine ⟨by word, by word, fun h => ?_⟩
      have := Hb h; cases this
  · simp only [hlt, _root_.decide_false, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    iapply HΦ
    iframe
    ipureintro
    have hj : sint.Z j = sint.Z fs.len := by word
    refine ⟨fun _ => rfl, fun h => ?_, fun h => by cases h⟩
    have h0 := Hj.2.2 h
    subst h0
    have : (nvs.filter P).length = 0 := by
      have := Hlen.1; rw [this]; word
    rw [List.eq_nil_of_length_eq_zero this]; rfl

end proof

end dsctl
end EtcdGrove
end Perennial
