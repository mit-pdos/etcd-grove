/-
Port of election_proof/proof_Progress__MaybeDecrTo.v.
-/
module

public import Spec.go_etcd_io.raft.v3.tracker.Progress__MaybeDecrTo

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

theorem tracker.Progress.MaybeDecrTo.wp_proof :
    tracker.Progress.MaybeDecrTo.spec (GF := GF) (hG := hG) := by
  intro pr p rejected matchHint
  wp_start as H
  iNamed H
  iNamed Hpr
  obtain ⟨h1, h2, h3, h4, h5, h6, h8, h9⟩ := (progressAbs_Some _ _ _).1 Habs
  wp_auto
  wp_if_destruct
  · have Hs : p.state = .replicate :=
      prstateW64_inj _ _ (by rw [← h2, Hif]; rfl)
    wp_if_destruct
    · -- exit 1
      have Hp : progressMaybeDecrTo p rejected matchHint = (false, p) := by
        simp only [progressMaybeDecrTo, Hs, ite_true]
        rw [ite_eq_left (by rw [← h3]; word)]
      rw [Hp]
      iapply HΦ
      iapply ownProgress_intro $$ Hpv Hinfl
      ipureintro; exact Habs
    · -- exit 2
      have Hp : progressMaybeDecrTo p rejected matchHint =
          (true, { p with next := p.matched + W64 1,
                          sentCommit := w64Min p.sentCommit (p.matched + W64 1 - W64 1) }) := by
        simp only [progressMaybeDecrTo, Hs, ite_true]
        rw [ite_eq_right (by rw [← h3]; exact Hif)]
      rw [Hp]
      wp_apply wp_min2_uint64
      iapply HΦ
      iapply ownProgress_intro pr _ _ $$ Hpv [Hinfl]
      · dsimp only
        iexact Hinfl
      ipureintro
      apply (progressAbs_Some _ _ _).2
      refine ⟨h1, h2, h3, by rw [h3], ?_, h6, h8, rfl⟩
      rw [h5, h3]
  · have Hs : p.state ≠ .replicate := by
      intro Hc; apply Hif; rw [h2, Hc]; rfl
    wp_if_destruct
    · -- exit 4: a genuine rejection while probing
      wp_apply wp_min2_uint64
      wp_apply wp_max2_uint64
      wp_apply wp_min2_uint64
      have Hp : progressMaybeDecrTo p (pv.Next' - W64 1) matchHint =
          (true, { p with next := w64Max (w64Min (pv.Next' - W64 1) (matchHint + W64 1)) (p.matched + W64 1),
                          sentCommit := w64Min p.sentCommit
                            (w64Max (w64Min (pv.Next' - W64 1) (matchHint + W64 1)) (p.matched + W64 1) - W64 1),
                          paused := false }) := by
        simp only [progressMaybeDecrTo, Hs, ite_false]
        rw [ite_eq_left (by rw [h4])]
      rw [Hp]
      iapply HΦ
      iapply ownProgress_intro pr _ _ $$ Hpv [Hinfl]
      · dsimp only
        iexact Hinfl
      ipureintro
      apply (progressAbs_Some _ _ _).2
      refine ⟨h1, h2, h3, by rw [h3], ?_, h6, rfl, rfl⟩
      dsimp only
      rw [h5, h3]
    · -- exit 3: stale
      have Hp : progressMaybeDecrTo p rejected matchHint = (false, p) := by
        simp only [progressMaybeDecrTo, Hs, ite_false]
        rw [ite_eq_right (by rw [← h4]; exact Hif)]
      rw [Hp]
      iapply HΦ
      iapply ownProgress_intro $$ Hpv Hinfl
      ipureintro; exact Habs

end proof

end EtcdGrove
end Perennial
