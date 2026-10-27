/-
Proof of `Spec/k8s_io/apimachinery/pkg/api/errors/NewBadRequest.lean`: the status literal, allocated. Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apimachinery.pkg.api.errors.NewBadRequest

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apierrors

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.api.errors.Assumptions]

theorem NewBadRequest.wp_proof : NewBadRequest.spec (GF := GF) (hG := hG) := by
  intro reason
  wp_start
  wp_auto
  wp_apply wp_alloc as %p Hp
  iapply HΦ
  iexists _
  iframe
  ipureintro
  exact ⟨rfl, rfl, rfl⟩

end proof

end apierrors
end EtcdGrove
end Perennial
