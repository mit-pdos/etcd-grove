/- Port of election_proof/proof_Progress__BecomeSnapshot.v. -/
import EtcdGrove.Raft.Spec.Progress__BecomeSnapshot
import EtcdGrove.Raft.Spec.Progress__ResetState

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

theorem tracker.Progress.BecomeSnapshot.wp_proof
    (wp_Progress_ResetState : tracker.Progress.ResetState.spec (GF := GF) (hG := hG)) :
    tracker.Progress.BecomeSnapshot.spec (GF := GF) (hG := hG) := by
  intro pr p snapshoti
  wp_start as Hpr
  wp_alloc pr_ptr as pr; wp_pures; wp_alloc snapshoti_ptr as snapshoti; wp_pures; wp_load; wp_pures
  -- `ResetState` is specified on `ownProgress` at the exact new record;
  -- open what it returns to step the field writes that follow
  rw [show tracker.StateSnapshot = #(prstateW64 PRState.snapshot) from rfl]
  wp_apply wp_Progress_ResetState _ _ PRState.snapshot $$ [$Hpr] as Hpr
  wp_pures; wp_load; wp_pures; wp_load; wp_pures
  unfold ownProgress
  iNamed Hpr
  wp_store; wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_store; wp_pures; wp_load; wp_pures
  wp_load; wp_pures; wp_store; wp_pures; iclear pr snapshoti
  iapply HΦ
  iexists _
  simp only [progressBecomeSnapshot]
  iframe Hpv Hinfl
  ipureintro
  -- Rocq `progress_abs_from Habs`
  rw [progressAbs_Some] at Habs ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := Habs
  simp only [progressResetState] at *
  exact ⟨h1, h2, h3, trivial, trivial, trivial, h7, h8, h9⟩

end proof

end EtcdGrove
end Perennial
