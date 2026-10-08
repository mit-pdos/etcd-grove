/-
Port of election_proof/proof_tracker_NewInflights.v.
-/
import EtcdGrove.Raft.Spec.tracker_NewInflights

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
theorem tracker.NewInflights.wp_proof : tracker.NewInflights.spec (GF := GF) (hG := hG) := by
  intro size maxBytes Hsz
  wp_start as _
  wp_auto
  -- `wp_auto` does not step a `GoAlloc` sitting in `return:` position -- the goal is
  -- still `WP exceptionDo (return: GoAlloc tracker.Inflights #{…})`. Allocate
  -- explicitly. The literal leaves `buffer' := slice.nil`, so the buffer is the empty
  -- slice.
  wp_apply wp_alloc as %l Hl
  iapply HΦ
  have Habs : inflightsNew size maxBytes =
      inflightsAbs
        { start' := 0, count' := 0, bytes' := 0, size' := size, maxBytes' := maxBytes,
          buffer' := slice.nil } := by
    unfold inflightsNew inflightsAbs; rfl
  rw [Habs]
  -- the ring-buffer invariant at a fresh `Inflights`: everything is zero and the
  -- buffer is empty, so only the `size` bounds have content -- exactly the premise.
  have Hok : InflightsOk (inflightsRingOf
      { start' := 0, count' := 0, bytes' := 0, size' := size, maxBytes' := maxBytes,
        buffer' := slice.nil } ([] : List tracker.inflight)) := by
    simp only [InflightsOk, inflightsRingOf, inflightsAbs, List.length_nil]
    word
  iapply ownInflights_reseal $$ Hl
  · iapply ownSlice_nil
  · iapply ownSliceCap_nil
  · ipureintro; exact ⟨Hok, rfl⟩

end proof

end EtcdGrove
end Perennial
