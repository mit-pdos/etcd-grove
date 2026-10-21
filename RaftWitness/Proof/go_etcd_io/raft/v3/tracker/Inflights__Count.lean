/-
`tracker.Inflights.Count`, Lean-first.
-/
module

public import Spec.go_etcd_io.raft.v3.tracker.Inflights__Count

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

/-- One field load; `W64 (sint.Z c) = c`. -/
theorem tracker.Inflights.Count.wp_proof :
    tracker.Inflights.Count.spec (GF := GF) (hG := hG) := by
  intro l i
  wp_start as Hin
  iNamed Hin
  iNamed Hin
  wp_auto
  subst Hring
  subst Hiabs
  rw [show W64 (inflightsRingOf iv buf).win.count = iv.count' by
    simp [inflightsRingOf, inflightsAbs, W64, sint.Z]]
  iapply HΦ
  iapply ownInflights_reseal $$ Hiv Hbuf Hbuf_cap; ipureintro; exact ⟨Hinfl_ok, rfl⟩

end proof

end EtcdGrove
end Perennial
