/-
The proof of `Spec/google_golang_org/grpc/internal/grpcutil/div.lean`.
-/
module

public import Spec.google_golang_org.grpc.internal.grpcutil.div

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.grpc.internal.grpcutil.Assumptions]

theorem grpcutil.div.wp_proof : grpcutil.div.spec (GF := GF) (hG := hG) := by
  intro d r hr
  wp_start as -
  unfold grpcHdr.durDiv
  wp_auto
  simp only [hr, ↓reduceIte]
  wp_auto
  wp_if_destruct
  · simp only [hr, ↓reduceIte]
    wp_auto
    rw [ite_eq_left (by word)]
    iapply HΦ
    itrivial
  · simp only [hr, ↓reduceIte]
    wp_auto
    rw [ite_eq_right (by word)]
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
