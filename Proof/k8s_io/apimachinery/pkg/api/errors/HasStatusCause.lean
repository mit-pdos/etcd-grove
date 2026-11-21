/-
Proof of `apierrors.HasStatusCause` (`Spec/k8s_io/apimachinery/pkg/api/errors/HasStatusCause.lean`) over its body
(prove-k8s2, 2026-11-20; until then a trust-boundary axiom).
-/
module

public import Spec.k8s_io.apimachinery.pkg.api.errors.HasStatusCause
public import Spec.k8s_io.apimachinery.pkg.api.errors.StatusCause
public import Proof.k8s_io.apimachinery.pkg.api.errors.Checks

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

theorem HasStatusCause.wp_proof
    (wp_StatusCause : StatusCause.spec (GF := GF) (hG := hG)) :
    HasStatusCause.spec (GF := GF) (hG := hG) := by
  intro err name
  wp_start as #Hok
  wp_auto
  wp_apply (wp_StatusCause err name) $$ [Hok] as %c %b #Hb
  · iframe
    iexact Hok
  iapply HΦ
  iexact Hb

end proof

end apierrors
end EtcdGrove
end Perennial
