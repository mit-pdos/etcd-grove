module
public import Spec.go_etcd_io.bbolt.internal.freelist.newShared

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

theorem newShared.wp_proof : newShared.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_apply (wp_map_make1 (K := w64) (V := Loc)) as %mp Hmp
  wp_apply (wp_map_make1 (K := w64) (V := w64)) as %ma Hma
  wp_apply (wp_map_make1 (K := w64) (V := Unit)) as %mc Hmc
  wp_apply wp_alloc as %s Hs
  iapply HΦ
  unfold ownShared ownSharedC
  dsimp only [FLState.empty]
  ihave Hpds : ([∗map] _t ↦ p;pd ∈ (∅ : GMap w64 Loc);(∅ : GMap w64 Pending),
      ownPending (GF := GF) p pd) $$ []
  · iapply (BigSepM2.bigSepM2_empty _).2; itrivial
  iexists (shared.mk interface.nil slice.nil ma mc mp), ∅
  isplitl
  · iexists ∅
    simp only [named]
    iframe
    isplitl []
    · iapply ownSlice_nil
    iapply ownSliceCap_nil
  ipureintro
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro id; simp [FLState.cached, FLState.allIds, FLState.pendingIds]
  · simp [FLState.allIds, FLState.pendingIds]
  · simp [FLState.allIds, FLState.pendingIds]
  · simp [PgidsIncr]
  · simp [FLState.allIds, FLState.pendingIds]
  · simp

end proof

end bbolt
end EtcdGrove
end Perennial
