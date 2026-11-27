/-
The proof of `Spec/google_golang_org/grpc/internal/grpcutil/ContentType.lean`.
-/
module

public import Spec.google_golang_org.grpc.internal.grpcutil.ContentType

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

theorem grpcutil.ContentType.wp_proof : grpcutil.ContentType.spec (GF := GF) (hG := hG) := by
  intro sub
  wp_start as -
  simp only [google_golang_org.grpc.internal.grpcutil.baseContentType]
  wp_auto
  wp_if_destruct
  · rw [show grpcHdr.contentTypeOf [] = go!"application/grpc" by simp [grpcHdr.contentTypeOf]]
    iapply HΦ
    itrivial
  · rw [show grpcHdr.contentTypeOf sub = go!"application/grpc+" ++ sub by
      simp [grpcHdr.contentTypeOf, Hif]]
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
