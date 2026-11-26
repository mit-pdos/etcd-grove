/-
Proof of `Spec/google_golang_org/grpc/mem/NewBinaryTieredBufferPool.lean` (grpc-mem, 2026-11-26).
-/
module

public import Spec.google_golang_org.grpc.mem.NewBinaryTieredBufferPool
public import Spec.google_golang_org.grpc.internal.mem.NewBinaryTieredBufferPool

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
variable [package_sem : google_golang_org.grpc.mem.Assumptions]

theorem grpc.mem.NewBinaryTieredBufferPool.wp_proof
    (wp_NewBinaryTieredBufferPool :
      grpc.internal.mem.NewBinaryTieredBufferPool.spec (GF := GF) (hG := hG)) :
    grpc.mem.NewBinaryTieredBufferPool.spec (GF := GF) (hG := hG) := by
  intro s xs Hxs Hlen
  wp_start as Hs
  wp_auto
  wp_apply wp_NewBinaryTieredBufferPool s xs Hxs Hlen $$ [Hs] as %l -
  · iexact Hs
  wp_end

end proof

end EtcdGrove
end Perennial
