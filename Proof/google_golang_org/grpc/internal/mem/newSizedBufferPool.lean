/-
Proof of `Spec/google_golang_org/grpc/internal/mem/newSizedBufferPool.lean` (grpc-mem, 2026-11-26).
-/
module

public import Spec.google_golang_org.grpc.internal.mem.newSizedBufferPool

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.grpc.internal.mem.Assumptions]

theorem grpc.internal.mem.newSizedBufferPool.wp_proof :
    grpc.internal.mem.newSizedBufferPool.spec (GF := GF) (hG := hG) := by
  intro size zero
  wp_start
  wp_auto
  wp_end

end proof

end EtcdGrove
end Perennial
