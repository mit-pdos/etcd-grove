/-
Proof of `Spec/google_golang_org/grpc/internal/mem/NewBinaryTieredBufferPool.lean` (grpc-mem, 2026-11-26).
-/
module

public import Spec.google_golang_org.grpc.internal.mem.NewBinaryTieredBufferPool
public import Spec.google_golang_org.grpc.internal.mem.newBinaryTiered
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

set_option goose.wp.extras true in
theorem grpc.internal.mem.NewBinaryTieredBufferPool.wp_proof
    (wp_newBinaryTiered : grpc.internal.mem.newBinaryTiered.spec (GF := GF) (hG := hG))
    (wp_newSizedBufferPool : grpc.internal.mem.newSizedBufferPool.spec (GF := GF) (hG := hG)) :
    grpc.internal.mem.NewBinaryTieredBufferPool.spec (GF := GF) (hG := hG) := by
  intro s xs Hxs Hlen
  wp_start as ⟨#Hpkg, Hs⟩
  wp_auto
  wp_func_lits
  wp_auto
  wp_apply wp_newBinaryTiered _ _ s xs Hxs Hlen $$ [Hs] as %l -
  · iframe Hs; iframe #
    imodintro
    iintro %n
    wp_func_call
    wp_call
    wp_auto
    wp_apply wp_newSizedBufferPool as %p -
    wp_auto
    ipureintro; exact ⟨_, rfl⟩
  wp_auto
  wp_end

end proof

end EtcdGrove
end Perennial
