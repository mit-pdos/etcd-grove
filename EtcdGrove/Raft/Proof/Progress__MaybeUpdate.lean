/-
Port of `election_proof/proof_Progress__MaybeUpdate.v`.

Lean notes: Perennial's Lean port has no `wp_max2_uint64`; the builtin `max` is
stepped into (`wp_func_call; wp_call`) and its `if` split with `wp_if_destruct`.
-/
import EtcdGrove.Raft.Spec.Progress__MaybeUpdate

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

theorem tracker.Progress.MaybeUpdate.wp_proof :
    tracker.Progress.MaybeUpdate.spec (GF := GF) (hG := hG) := by
  intro pr p n
  wp_start as H
  iNamed H
  iNamed Hpr
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := (progressAbs_Some _ _ _).1 Habs
  wp_alloc pr_ptr as pr; wp_pures; wp_alloc n_ptr as n; wp_pures; wp_load; wp_load; wp_pures
  wp_load; wp_pures
  wp_if_destruct
  · -- `n <= pr.Match`: stale
    have Hd : decide (uint.Z p.matched < uint.Z n) = false := by
      rw [← h3]; simp only [decide_eq_false_iff_not]; word
    have Hp : progressMaybeUpdate p n = p := by
      rw [progressMaybeUpdate, ← h3]; split <;> first | rfl | (exfalso; word)
    rw [Hd, Hp]
    iapply HΦ
    iapply ownProgress_intro $$ Hpv Hinfl
    ipureintro; exact Habs
  · wp_load; wp_pures; wp_load; wp_pures; wp_store; wp_pures; wp_load; wp_pures; wp_load; wp_pures
    wp_load; wp_pures; iclear n
    -- `max` is the builtin: step into it
    wp_func_call
    wp_call
    have Hd : decide (uint.Z p.matched < uint.Z n) = true := by
      rw [← h3]; simp only [decide_eq_true_eq]; word
    have Hp : progressMaybeUpdate p n =
        { p with matched := n, next := w64Max p.next (n + W64 1), paused := false } := by
      rw [progressMaybeUpdate, ← h3]; split <;> first | rfl | (exfalso; word)
    rw [Hd, Hp]
    wp_if_destruct <;>
    · wp_load; wp_pures; wp_store; wp_pures; wp_load; wp_pures; wp_store; wp_pures
      iapply HΦ
      iapply ownProgress_intro pr _ _ $$ Hpv [Hinfl]
      · dsimp only
        iexact Hinfl
      ipureintro
      apply (progressAbs_Some _ _ _).2
      refine ⟨h1, h2, rfl, ?_, h5, h6, h7, rfl, rfl⟩
      simp only [w64Max]
      rw [← h4]
      split <;> first | rfl | (exfalso; word)

end proof

end EtcdGrove
end Perennial
