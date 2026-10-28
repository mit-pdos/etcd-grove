/-
Proof of `Spec/k8s_io/component_helpers/scheduling/corev1/getFilteredTaints.lean`. Lean-first.
-/
module

public import Spec.k8s_io.component_helpers.scheduling.corev1.getFilteredTaints

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

theorem getFilteredTaints.wp_proof : getFilteredTaints.spec (GF := GF) (hG := hG) := by
  intro ts dq tvs f P
  wp_start as ⟨Hts, #Hf⟩
  iunfold taintFilterOk at Hf
  icases Hf with ⟨%Hfnn, #Hf⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hts
  wp_auto
  rw [decide_eq_false Hfnn]
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %l0 ⟨Hl0, Hcap0⟩
  simp only [go.arrayLiteralSize, List.foldl, show max (max (0:Int) 0) 0 = 0 by decide]
  wp_auto
  ihave HI : (∃ (j : w64) (fs : GoSlice), "i" ∷ i_ptr ↦ j ∗ "filteredTaints" ∷ filteredTaints_ptr ↦ fs ∗
      "Hfs" ∷ fs ↦* (tvs.take (sint.nat j)).filter P ∗
      "Hcap" ∷ ownSliceCap k8s_io.api.core.v1.Taint fs (DFrac.own 1) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z ts.len⌝ ∗
      "Hts" ∷ ts ↦*{dq} tvs ∗ "inclusionFilter" ∷ inclusionFilter_ptr ↦ f : IProp GF)
    $$ [-HΦ]
  · iexists W64 0, _
    iframe
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.filter_nil,
      show (0 : Int).toNat = 0 from rfl, List.replicate_zero]
    iframe
    ipureintro; constructor <;> word
  wp_for HI
  by_cases hlt : sint.Z j < sint.Z ts.len
  · simp only [hlt, _root_.decide_true, ↓reduceIte]
    wp_auto
    obtain ⟨v, hv⟩ : ∃ v, tvs[sint.nat j]? = some v :=
      ⟨_, List.getElem?_eq_getElem (by word)⟩
    have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z ts.len := ⟨Hj.1, hlt⟩
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply (wp_load_slice_index ts (sint.Z j) tvs _ v Hj.1) $$ [Hts] as Hts
    · iframe; ipureintro; simpa [sint.nat] using hv
    wp_apply Hf $$ %taint_ptr %v [$taint] as taint
    have htake : tvs.take (sint.nat (j + W64 1)) = tvs.take (sint.nat j) ++ [v] := by
      rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word]
      rw [List.take_add_one, hv]; rfl
    cases hP : P v
    · wp_auto
      wp_for_post
      iframe
      iexists j + W64 1, fs
      iframe
      rw [htake, List.filter_append]
      simp only [List.filter_cons, hP, Bool.false_eq_true, ↓reduceIte, List.filter_nil,
        List.append_nil]
      iframe
      ipureintro; constructor <;> word
    · wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %l1 ⟨Hl1, -⟩
      simp only [go.arrayLiteralSize, List.foldl]
      wp_auto
      wp_apply wp_slice_append $$ [$Hfs $Hcap $Hl1] as %fs' ⟨Hfs, Hcap, -⟩
      wp_for_post
      iframe
      iexists j + W64 1, fs'
      iframe
      rw [htake, List.filter_append]
      simp only [List.filter_cons, hP, ↓reduceIte, List.filter_nil]
      iframe
      ipureintro; constructor <;> word
  · simp only [hlt, _root_.decide_false, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    iapply HΦ
    have hj : sint.nat j = tvs.length := by word
    rw [hj, List.take_length]
    iframe

end proof

end dsctl
end EtcdGrove
end Perennial
