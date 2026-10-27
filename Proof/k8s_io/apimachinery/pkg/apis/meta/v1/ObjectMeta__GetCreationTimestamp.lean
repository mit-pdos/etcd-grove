/-
Proof of `Spec/k8s_io/apimachinery/pkg/apis/meta/v1/ObjectMeta__GetCreationTimestamp.lean`. Lean-first.
-/
module

public import Spec.k8s_io.apimachinery.pkg.apis.meta.v1.ObjectMeta__GetCreationTimestamp

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace metav1

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.apis.«meta».v1.Assumptions]

theorem ObjectMeta.GetCreationTimestamp.wp_proof : ObjectMeta.GetCreationTimestamp.spec (GF := GF) (hG := hG) := by
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
