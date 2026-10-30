/-
Proof of `Spec/k8s_io/apimachinery/pkg/util/resourceversion/isDigit.lean`. Lean-first.
-/
module

public import Spec.k8s_io.apimachinery.pkg.util.resourceversion.isDigit

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace resourceversion

open Iris Iris.BI Iris.ProofMode k8s_io.apimachinery.pkg.util.resourceversion

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.util.resourceversion.Assumptions]

theorem isDigit.wp_proof : isDigit.spec (GF := GF) (hG := hG) := by
  intro b
  wp_start
  wp_auto
  wp_if_destruct
  · have h : decide (uint.Z b ≤ uint.Z (W8 57)) = digitB b := by
      unfold digitB; rw [decide_eq_decide]; word
    rw [h]; iapply HΦ; itrivial
  · have h : false = digitB b := by
      unfold digitB; symm; rw [decide_eq_false_iff_not]; word
    rw [h]; iapply HΦ; itrivial

end proof

end resourceversion
end EtcdGrove
end Perennial
