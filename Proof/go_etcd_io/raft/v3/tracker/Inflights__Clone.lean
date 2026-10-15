/-
`tracker.Inflights.Clone`, Lean-first.
-/
module

public import Spec.go_etcd_io.raft.v3.tracker.Inflights__Clone

@[expose] public section

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

/-- The struct copy, then `append` onto `nil` copies the buffer's contents into a fresh
slice of capacity one owns; the copy denotes the same ring (`inflightsRingOf` reads only
the buffer's length). -/
theorem tracker.Inflights.Clone.wp_proof :
    tracker.Inflights.Clone.spec (GF := GF) (hG := hG) := by
  intro l i
  wp_start as Hin
  iNamed Hin
  iNamed Hin
  wp_auto
  ihave Hcapnil : ownSliceCap tracker.inflight slice.nil (DFrac.own 1) $$ []
  · iapply ownSliceCap_nil
  ihave Hnil : (slice.nil ↦* ([] : List tracker.inflight)) $$ []
  · iapply ownSlice_nil
  wp_apply wp_slice_append (V := tracker.inflight) slice.nil [] iv.buffer' buf (DFrac.own 1)
    $$ [$Hnil $Hcapnil $Hbuf] as %s' ⟨Hs', Hcap', Hbuf⟩
  simp only [List.nil_append]
  iapply HΦ
  subst Hiabs
  isplitl [Hiv Hbuf Hbuf_cap]
  · iapply ownInflights_reseal $$ Hiv Hbuf Hbuf_cap; ipureintro
    subst Hring; exact ⟨Hinfl_ok, rfl⟩
  · iapply ownInflights_reseal $$ ins Hs' Hcap'; ipureintro
    subst Hring; exact ⟨Hinfl_ok, rfl⟩

end proof

end EtcdGrove
end Perennial
