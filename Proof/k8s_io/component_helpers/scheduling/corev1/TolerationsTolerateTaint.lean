/-
Proof of `Spec/k8s_io/component_helpers/scheduling/corev1/TolerationsTolerateTaint.lean`. Lean-first.
-/
module

public import Spec.k8s_io.component_helpers.scheduling.corev1.TolerationsTolerateTaint
public import Spec.k8s_io.api.core.v1.Toleration__ToleratesTaint

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

theorem TolerationsTolerateTaint.wp_proof
    (wp_ToleratesTaint : corev1.Toleration.ToleratesTaint.spec (GF := GF) (hG := hG)) :
    TolerationsTolerateTaint.spec (GF := GF) (hG := hG) := by
  intro logger ts dq tols n dq' nv en
  wp_start as ⟨Hts, Hn⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hts
  wp_auto
  rename_i ip2
  ihave HI : (∃ (j x : w64), "i" ∷ i_ptr ↦ j ∗ "i2" ∷ ip2 ↦ x ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z ts.len⌝ ∗
      "Hts" ∷ ts ↦*{dq} tols ∗ "Hn" ∷ n ↦{dq'} nv ∗
      "enableComparisonOperators" ∷ enableComparisonOperators_ptr ↦ en ∗ "taint" ∷ taint_ptr ↦ n ∗
      "tolerations" ∷ tolerations_ptr ↦ ts ∗ "logger" ∷ logger_ptr ↦ logger : IProp GF)
    $$ [-HΦ]
  · iexists W64 0, _
    iframe
    ipureintro; constructor <;> word
  wp_for HI
  by_cases hlt : sint.Z j < sint.Z ts.len
  · simp only [hlt, _root_.decide_true, ↓reduceIte]
    wp_auto
    obtain ⟨v, hv⟩ : ∃ v, tols[sint.nat j]? = some v :=
      ⟨_, List.getElem?_eq_getElem (by word)⟩
    have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z ts.len := ⟨Hj.1, hlt⟩
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply (wp_load_slice_index ts (sint.Z j) tols _ v Hj.1) $$ [Hts] as Hts
    · iframe; ipureintro; simpa [sint.nat] using hv
    simp only [hb, _root_.and_self, ↓reduceIte]
    icases ownSlice_elem_acc (sint.Z j) v ts dq tols Hj.1 (by simpa [sint.nat] using hv) $$ Hts
      with ⟨Hv, Hts⟩
    wp_auto
    wp_apply (wp_ToleratesTaint _ dq v logger n dq' nv en) $$ [$Hv $Hn] as %b ⟨Hv, Hn⟩
    ihave Hts := Hts $$ %v Hv
    rw [show (sint.Z j).toNat = sint.nat j from rfl, list_set_lookup_self tols _ v hv]
    cases b
    · wp_auto
      wp_for_post
      iframe
      iexists j + W64 1, j
      iframe
      ipureintro; constructor <;> word
    · wp_auto
      wp_for_post
      iapply HΦ
      iframe
      ipureintro
      intro h; subst h; simp at hv
  · simp only [hlt, _root_.decide_false, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    iapply HΦ
    iframe
    ipureintro; intro; rfl

end proof

end dsctl
end EtcdGrove
end Perennial
