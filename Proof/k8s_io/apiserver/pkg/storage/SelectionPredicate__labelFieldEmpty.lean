/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/SelectionPredicate__labelFieldEmpty.lean`. Lean-first (no Rocq
counterpart).
-/
module

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

theorem storage.SelectionPredicate.labelFieldEmpty.wp_proof
    : storage.SelectionPredicate.labelFieldEmpty.spec (GF := GF) (hG := hG) := by
  intro pp dq p le fe lm fm
  wp_start as ⟨Hp, #Hl, #Hf⟩
  iunfold labelSelOk at Hl
  iunfold fieldSelOk at Hf
  icases Hl with ⟨%li, %hli, #HlE, #HlM⟩
  icases Hf with ⟨%fi, %hfi, #HfE, #HfM⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hp with ⟨Hp, %Hnn⟩
  iStructNamed Hp
  wp_auto
  rw [hli, hfi]
  wp_auto
  wp_bind
  iapply HlE
  inext
  cases le
  · wp_auto
    iapply HΦ
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    rw [hli, hfi]
    iframe
  · wp_auto
    wp_bind
    iapply HfE
    inext
    wp_auto
    iapply HΦ
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    rw [hli, hfi]
    iframe

end proof

end EtcdGrove
end Perennial
