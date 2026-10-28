/-
Port of election_proof/proof_tracker_NewInflights.v.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.tracker.NewInflights

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
theorem tracker.NewInflights.wp_proof : tracker.NewInflights.spec (GF := GF) (hG := hG) := by
  intro size maxBytes Hsz
  wp_start as _
  wp_auto
  -- `wp_auto` allocated the returned `Inflights` (`«$r0»`). The literal leaves
  -- `buffer' := slice.nil`, so the buffer is the empty slice.
  irename «$r0» => Hl
  generalize «$r0_ptr» = l at *
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
