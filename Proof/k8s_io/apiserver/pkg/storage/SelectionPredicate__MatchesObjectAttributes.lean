/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/SelectionPredicate__MatchesObjectAttributes.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.SelectionPredicate__MatchesObjectAttributes
public import Spec.k8s_io.apiserver.pkg.storage.SelectionPredicate__labelFieldEmpty

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode k8s

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.Assumptions]

theorem storage.SelectionPredicate.MatchesObjectAttributes.wp_proof
    (wp_labelFieldEmpty : storage.SelectionPredicate.labelFieldEmpty.spec (GF := GF) (hG := hG))
    : storage.SelectionPredicate.MatchesObjectAttributes.spec (GF := GF) (hG := hG) := by
  intro pp dq p le fe lm fm lp fp L F
  wp_start as ⟨Hp, #Hl, #Hf, #HL, #HF⟩
  (try wp_auto)
  wp_apply (wp_labelFieldEmpty pp dq p le fe lm fm) $$ [$Hp $Hl $Hf] as Hp
  iunfold labelSelOk at Hl
  iunfold fieldSelOk at Hf
  icases Hl with ⟨%li, %hli, #HlE, #HlM⟩
  icases Hf with ⟨%fi, %hfi, #HfE, #HfM⟩
  cases hlf : (le && fe)
  · (try wp_auto)
    icases typedPointsto_not_null_dup _ _ _ $$ Hp with ⟨Hp, %Hnn⟩
    iStructNamed Hp
    (try wp_auto)
    rw [hli, hfi]
    (try wp_auto)
    wp_bind
    iapply HlM $$ HL
    inext
    cases hl : lm L
    · (try wp_auto)
      simp only [Bool.false_or, Bool.false_and, Bool.true_and]
      iapply HΦ
      iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      rw [hli, hfi]
      iframe
    · (try wp_auto)
      wp_bind
      iapply HfM $$ HF
      inext
      (try wp_auto)
      simp only [Bool.false_or, Bool.false_and, Bool.true_and]
      iapply HΦ
      iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      rw [hli, hfi]
      iframe
  · (try wp_auto)
    iapply HΦ
    iexact Hp

end proof

end EtcdGrove
end Perennial
