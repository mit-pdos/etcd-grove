/-
Port of election_proof/proof_Progress__BecomeProbe.v.

Lean notes: the framework's Rocq `wp_max2_uint64` has no Lean counterpart; it is the
private `wp_max2_uint64` below (the mirror of `wp_min2_uint64`, `InvTracker.lean`).
-/
import EtcdGrove.Raft.Spec.Progress__BecomeProbe
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
/-- `max` on `uint64` (Rocq: the framework's `wp_max2_uint64`). -/
private theorem wp_max2_uint64 (x y : w64) :
    {{ (True : IProp GF) }}
      (App (App (Val #(functions go.max [go.uint64, go.uint64])) (Val #x)) (Val #y))
    {{ RET #(w64Max x y); True }} := by
  wp_start
  wp_if_destruct
  · rw [show w64Max x y = x by unfold w64Max; simp_all]
    iapply HΦ; itrivial
  · rw [show w64Max x y = y by unfold w64Max; rw [if_neg (by omega)]]
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
  iunfold ownProgress at Hpr
  icases Hpr with ⟨%pv, Hpr⟩
  iNamed Hpr
  have Habs0 := (progressAbs_Some _ _ _).1 Habs
  obtain ⟨Hl, Hst, Hm, Hn, Hsc, Hps, -⟩ := Habs0
  unfold progressBecomeProbe progressBecomeProbeNext
  wp_auto
  by_cases Hs : p.state = .snapshot
  · -- `StateSnapshot`: probe from past the pending snapshot
    have Hs2 : pv.State' = W64 2 := by rw [Hst, Hs]; rfl
    rw [decide_eq_true Hs2]
    wp_auto
    ihave Hpr := ownProgress_intro pr pv p $$ Hpv Hinfl %Habs
    rw [show tracker.StateProbe = #(prstateW64 .probe) from rfl]
    wp_apply wp_Progress_ResetState _ _ .probe $$ [$Hpr] as Hpr
    iunfold ownProgress at Hpr
    icases Hpr with ⟨%pv', Hpr⟩
    iNamed Hpr
    wp_auto
    wp_apply wp_max2_uint64
    wp_apply wp_min2_uint64
    iapply HΦ
    unfold ownProgress
    iexists _
    simp only [named]
    iframe Hpv
    isplitl [Hinfl]
    · simp only [progressResetState]
      iexact Hinfl
    ipureintro
    have H' := (progressAbs_Some _ _ _).1 Habs
    apply (progressAbs_Some _ _ _).2
    simp only [progressResetState, Hs, ite_true] at H' ⊢
    obtain ⟨h1, h2, h3, -, h5, h6, h8, -⟩ := H'
    refine ⟨h1, h2, h3, ?_, ?_, h6, h8, trivial⟩ <;> simp only [h3, h5, Hps]
  · -- any other state: probe from `Match + 1`
    rw [decide_eq_false (by
      rw [Hst]; intro Hc; exact Hs (prstateW64_inj _ _ (Hc.trans (by rfl))))]
    wp_auto
    ihave Hpr := ownProgress_intro pr pv p $$ Hpv Hinfl %Habs
    rw [show tracker.StateProbe = #(prstateW64 .probe) from rfl]
    wp_apply wp_Progress_ResetState _ _ .probe $$ [$Hpr] as Hpr
    iunfold ownProgress at Hpr
    icases Hpr with ⟨%pv', Hpr⟩
    iNamed Hpr
    wp_auto
    wp_apply wp_min2_uint64
    iapply HΦ
    unfold ownProgress
    iexists _
    simp only [named]
    iframe Hpv
    isplitl [Hinfl]
    · simp only [progressResetState]
      iexact Hinfl
    ipureintro
    have H' := (progressAbs_Some _ _ _).1 Habs
    apply (progressAbs_Some _ _ _).2
    simp only [progressResetState, Hs, ite_false] at H' ⊢
    obtain ⟨h1, h2, h3, -, h5, h6, h8, -⟩ := H'
    refine ⟨h1, h2, h3, ?_, ?_, h6, h8, trivial⟩ <;> simp only [h3, h5]

end proof

end EtcdGrove
end Perennial
