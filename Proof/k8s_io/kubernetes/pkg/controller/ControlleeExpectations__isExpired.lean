/-
Proof of `Spec/k8s_io/kubernetes/pkg/controller/ControlleeExpectations__isExpired.lean`. Lean-first.
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.ControlleeExpectations__isExpired
public import Spec.k8s_io.utils.clock.RealClock__Since

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode k8s_io.kubernetes.pkg.controller

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.Assumptions]

theorem ControlleeExpectations.isExpired.wp_proof
    (wp_Since : clock.RealClock.Since.spec (GF := GF) (hG := hG)) :
    ControlleeExpectations.isExpired.spec (GF := GF) (hG := hG) := by
  intro e k
  wp_start as #Hce
  iunfold isCE at Hce
  icases Hce with ⟨#Hk, ⟨%t, #Ht⟩, #Hinv⟩
  wp_auto
  wp_apply wp_Since as %d
  iintro -
  wp_auto
  iapply HΦ; itrivial

end proof

end dsctl
end EtcdGrove
end Perennial
