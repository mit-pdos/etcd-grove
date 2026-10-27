/-
Proof of `Spec/k8s_io/apimachinery/pkg/util/resourceversion/CompareResourceVersion.lean`.
Lean-first.
-/
module

public import Spec.k8s_io.apimachinery.pkg.util.resourceversion.CompareResourceVersion
public import Spec.k8s_io.apimachinery.pkg.util.resourceversion.isWellFormed
public import Perennial.Spec.strings.Compare

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace resourceversion

open Iris Iris.BI Iris.ProofMode k8s_io.apimachinery.pkg.util.resourceversion

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.util.resourceversion.Assumptions]

theorem CompareResourceVersion.wp_proof
    (wp_isWellFormed : isWellFormed.spec (GF := GF) (hG := hG))
    (wp_Compare : strings.Compare.spec (GF := GF) (hG := hG)) :
    CompareResourceVersion.spec (GF := GF) (hG := hG) := by
  intro a b
  wp_start
  ihave #Hstr : isPkgInit (PROP := IProp GF) pkg_id.strings $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_isWellFormed
  cases ha : wellFormed a
  · wp_auto
    simp only [compareRV, ha, ↓reduceIte, Bool.false_eq_true]
    iapply HΦ; itrivial
  · wp_auto
    wp_apply wp_isWellFormed
    cases hb : wellFormed b
    · wp_auto
      simp only [compareRV, ha, hb, ↓reduceIte, Bool.false_eq_true]
      iapply HΦ; itrivial
    · wp_auto
      wp_func_call
      wp_call
      by_cases hla : a.length < 2 ^ 63
      · rw [if_pos hla]
        wp_auto
        wp_func_call
        wp_call
        by_cases hlb : b.length < 2 ^ 63
        · rw [if_pos hlb]
          wp_auto
          have hcmp := lexCmp_eq_cmpNat a b ha hb
          simp only [compareRV, ha, hb, ↓reduceIte]
          rw [← hcmp]
          unfold lexCmp
          wp_if_destruct
          · have h1 : a.length < b.length := by
              rw [sintZ_len hla, sintZ_len hlb] at Hif; simp at Hif; omega
            simp only [h1, ↓reduceIte]
            iapply HΦ; itrivial
          · have h1 : ¬ a.length < b.length := by
              rw [sintZ_len hla, sintZ_len hlb] at Hif; simp at Hif; omega
            simp only [h1, ↓reduceIte]
            wp_if_destruct
            · have h2 : a.length > b.length := by
                rw [sintZ_len hla, sintZ_len hlb] at Hif; simp at Hif; omega
              simp only [h2, ↓reduceIte]
              iapply HΦ; itrivial
            · have h2 : ¬ a.length > b.length := by
                rw [sintZ_len hla, sintZ_len hlb] at Hif; simp at Hif; omega
              simp only [h2, ↓reduceIte]
              wp_apply wp_Compare
              iapply HΦ; itrivial
        · rw [if_neg hlb]
          wp_apply wp_AngelicExit
      · rw [if_neg hla]
        wp_apply wp_AngelicExit

end proof

end resourceversion
end EtcdGrove
end Perennial
