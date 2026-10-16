/-
Port of election_proof/proof_Progress__BecomeProbe.v.

Lean notes: the framework's Rocq `wp_max2_uint64` has no Lean counterpart; it is the
private `wp_max2_uint64` below (the mirror of `wp_min2_uint64`, `InvTracker.lean`).
-/
module

public import Spec.go_etcd_io.raft.v3.tracker.Progress__BecomeProbe
public import Spec.go_etcd_io.raft.v3.tracker.Progress__ResetState

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
/-- `max` on `uint64` (Rocq: the framework's `wp_max2_uint64`). -/
private theorem wp_max2_uint64 (x y : w64) :
    {{ (True : IProp GF) }}
      (App (App (Val #(functions go.max [go.uint64, go.uint64])) (Val #x)) (Val #y))
    {{ RET #(w64Max x y); True }} := by
  wp_start
  wp_if_destruct
  · rw [show w64Max x y = x by unfold w64Max; simp_all]
    iapply HΦ; itrivial
  · rw [show w64Max x y = y by unfold w64Max; rw [ite_eq_right (by omega)]]
    iapply HΦ; itrivial

/-- Both arms call `ResetState(StateProbe)` (exact spec), then write `Next`; the shared
tail writes `sentCommit`. `max`/`min` are stepped with `wp_max2_uint64` (above) and
`wp_min2_uint64` (`InvTracker.lean`), whose results are `w64Max`/`w64Min` by
definition. -/
theorem tracker.Progress.BecomeProbe.wp_proof
    (wp_Progress_ResetState : tracker.Progress.ResetState.spec (GF := GF) (hG := hG)) :
    tracker.Progress.BecomeProbe.spec (GF := GF) (hG := hG) := by
  intro pr p
  wp_start as Hpr
  unfold progressBecomeProbe progressBecomeProbeNext
  wp_auto
  -- (raft#243) one path: `ResetState(StateProbe)`, `Next = Match + 1`
  rw [show tracker.StateProbe = #(prstateW64 .probe) from rfl]
  wp_apply wp_Progress_ResetState _ _ .probe $$ [$Hpr] as Hpr
  iunfold ownProgress at Hpr
  icases Hpr with ⟨%pv', Hpr⟩
  iNamed Hpr
  have H' := (progressAbs_Some _ _ _).1 Habs
  wp_auto
  wp_apply wp_min2_uint64
  iapply HΦ
  unfold ownProgress
  iexists _
  simp only [named]
  iframe Hpv
  isplitl [Hinfl]
  · iexact Hinfl
  ipureintro
  apply (progressAbs_Some _ _ _).2
  simp only [progressResetState] at H' ⊢
  obtain ⟨h1, h2, h3, -, h5, h6, h7⟩ := H'
  refine ⟨h1, h2, h3, ?_, ?_, h6, h7⟩ <;> simp only [h3, h5]

end proof

end EtcdGrove
end Perennial
