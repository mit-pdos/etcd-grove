/-
Proof of `Spec/k8s_io/apimachinery/pkg/api/errors/NewResourceExpired.lean`: the status literal, allocated. Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apimachinery.pkg.api.errors.NewResourceExpired

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apierrors

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.api.errors.Assumptions]

theorem NewResourceExpired.wp_proof : NewResourceExpired.spec (GF := GF) (hG := hG) := by
  intro message
  wp_start
  wp_auto
  iapply HΦ
  iexists _
  iframe
  ipureintro
  exact ⟨rfl, rfl, rfl⟩

end proof

end apierrors
end EtcdGrove
end Perennial
