/-
Proof of `Spec/k8s_io/apimachinery/pkg/apis/meta/v1/ObjectMeta__GetUID.lean`. Lean-first.
-/
module

public import Spec.k8s_io.apimachinery.pkg.apis.meta.v1.ObjectMeta__GetUID

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace metav1

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.apis.«meta».v1.Assumptions]

theorem ObjectMeta.GetUID.wp_proof : ObjectMeta.GetUID.spec (GF := GF) (hG := hG) := by
  intro l v dq
  wp_start as Hl
  -- (the field is read through the struct's points-to split: `wp_load` finds no field access
  -- of a struct points-to at a fraction other than `1`; notes/perennial-changes.md)
  icases typedPointsto_not_null_dup _ _ _ $$ Hl with ⟨Hl, %Hnn⟩
  iStructNamed Hl
  wp_auto
  iapply HΦ
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

end proof

end metav1
end EtcdGrove
end Perennial
