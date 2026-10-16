/- New with raft#243. -/
module

public import Spec.go_etcd_io.raft.v3.tracker.Progress__OnSnapshotApplied

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

theorem tracker.Progress.OnSnapshotApplied.wp_proof :
    tracker.Progress.OnSnapshotApplied.spec (GF := GF) (hG := hG) := by
  intro pr p i
  wp_start as Hpr
  iunfold ownProgress at Hpr
  icases Hpr with ⟨%pv, Hpr⟩
  iNamed Hpr
  wp_auto
  iapply HΦ
  unfold ownProgress
  iexists _
  simp only [named, progressOnSnapshotApplied]
  iframe Hpv Hinfl
  ipureintro
  rw [progressAbs_Some] at Habs ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := Habs
  exact ⟨h1, h2, rfl, rfl, h5, h6, h7⟩

end proof

end EtcdGrove
end Perennial
