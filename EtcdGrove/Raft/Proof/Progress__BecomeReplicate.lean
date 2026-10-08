/- Port of election_proof/proof_Progress__BecomeReplicate.v. -/
import EtcdGrove.Raft.Spec.Progress__BecomeReplicate
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

theorem tracker.Progress.BecomeReplicate.wp_proof
    (wp_Progress_ResetState : tracker.Progress.ResetState.spec (GF := GF) (hG := hG)) :
    tracker.Progress.BecomeReplicate.spec (GF := GF) (hG := hG) := by
  intro pr p
  wp_start as Hpr
  wp_alloc pr_ptr as pr; wp_pures; wp_load; wp_pures
  -- `ResetState` is specified on `ownProgress` at the exact new record;
  -- open what it returns to step the field writes that follow
  rw [show tracker.StateReplicate = #(prstateW64 .replicate) from rfl]
  wp_apply wp_Progress_ResetState _ _ .replicate $$ [$Hpr] as Hpr
  wp_pures; wp_load; wp_pures
  unfold ownProgress
  iNamed Hpr
  wp_load; wp_pures; wp_load; wp_pures; wp_store; wp_pures; iclear pr
  iapply HΦ
  iexists _
  simp only [progressBecomeReplicate]
  iframe Hpv Hinfl
  ipureintro
  -- Rocq `progress_abs_from Habs`
  rw [progressAbs_Some] at Habs ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := Habs
  exact ⟨h1, h2, h3, by simp only [h3, progressResetState], h5, h6, h7, h8, h9⟩

end proof

end EtcdGrove
end Perennial
