/-
Proof of `Spec/.../mvcc/kvHashIncludes.lean` (pr-verify/etcd-22562). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.kvHashIncludes
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.BytesToRev
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.BytesToBucketKey
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Revision__GreaterThan

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

/-- `Revision{Main: m + 1}.GreaterThan(r)`, of a revision with a non-negative sub, is `r`'s main at
or below `m` (no overflow). -/
theorem mvcc.Rev.gt_succ (m : w64) (r : mvcc.Rev) (hs : 0 ≤ sint.Z r.sub)
    (hm : sint.Z m < 2 ^ 63 - 1) :
    mvcc.Rev.gt ⟨m + W64 1, W64 0⟩ r = decide (sint.Z r.main ≤ sint.Z m) := by
  have h1 : sint.Z (m + W64 1) = sint.Z m + 1 := by word
  unfold mvcc.Rev.gt
  simp only []
  by_cases h : sint.Z r.main ≤ sint.Z m
  · have : sint.Z r.main < sint.Z (m + W64 1) := by omega
    rw [decide_eq_true this, decide_eq_true h]
  · have h2 : ¬ sint.Z r.main < sint.Z (m + W64 1) := by omega
    have h3 : ¬ sint.Z r.sub < sint.Z (W64 0) := by
      rw [show sint.Z (W64 0) = 0 by decide]; omega
    rw [decide_eq_false h2, decide_eq_false h3, decide_eq_false h]
    simp

/-- `hashIncl` of a pair at or below the hasher's revision, as the code computes it. -/
theorem mvcc.hashIncl_decide (c rev : w64) (K : mvcc.Rev → Prop) [DecidablePred K] (r : mvcc.Rev)
    (t : Bool) (Hu : sint.Z r.main ≤ sint.Z rev) :
    decide (mvcc.hashIncl (sint.Z c) (sint.Z rev) K r t) =
      ((decide (sint.Z c < sint.Z r.main) || decide (K r)) && Bool.not (decide (r.main = c) && t)) := by
  have hiff : sint.Z r.main = sint.Z c ↔ r.main = c := ⟨fun h => by word, fun h => by rw [h]⟩
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  unfold mvcc.hashIncl
  by_cases h1 : sint.Z c < sint.Z r.main <;> by_cases h2 : K r <;> by_cases h3 : r.main = c <;>
    cases t <;> simp [h1, h2, h3, hiff, Hu] <;> (rw [← h3]; exact Hu)

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.kvHashIncludes.wp_proof
    (hB2R : mvcc.BytesToRev.spec (GF := GF) (hG := hG))
    (hB2BK : mvcc.BytesToBucketKey.spec (GF := GF) (hG := hG))
    (hGT : mvcc.Revision.GreaterThan.spec (GF := GF) (hG := hG)) :
    mvcc.kvHashIncludes.spec (GF := GF) (hG := hG) := by
  intro c rev keep dq A s r rest dk hrest hm hsub hc0 hc1 hrev
  wp_start as ⟨Hkeep, Hs⟩
  -- (`wp_auto` does not take the first allocation here: done by hand)
  wp_bind (GoInstruction (GoAlloc _) _)
  wp_alloc k_ptr as Hk
  wp_auto
  wp_apply (hB2R s r rest dk hrest hm hsub) $$ [$Hs] as Hs
  have Hup := mvcc.Rev.gt_succ rev r hsub hrev
  have Hlo := mvcc.Rev.gt_succ c r hsub hc1
  -- `upper.GreaterThan(kr)`: the pointer wrapper, then the value method
  rw [method_unfold (t := go.GoType.PointerType Revision.ty) (m := go!"GreaterThan")]
  wp_call
  wp_auto
  wp_apply (hGT _ (mvcc.revVal r))
  rw [show (mvcc.revOf { Main' := rev + W64 1, Sub' := 0 }).gt (mvcc.revOf (mvcc.revVal r)) =
      decide (sint.Z r.main ≤ sint.Z rev) from Hup]
  by_cases Hu : sint.Z r.main ≤ sint.Z rev
  rotate_left
  · simp only [Hu, decide_false, Bool.not_false]
    wp_auto
    have : decide (mvcc.hashIncl (sint.Z c) (sint.Z rev) (mvcc.keptBy A) r
        (decide (rest = [mvcc.markTomb]))) = false := by
      simp [mvcc.hashIncl, Hu]
    rw [this]
    iapply HΦ
    iframe
  simp only [Hu, decide_true, Bool.not_true]
  wp_auto
  wp_apply (hB2BK s r rest dk hrest hm hsub) $$ [$Hs] as Hs
  -- `lower.GreaterThan(kr)`
  rw [method_unfold (t := go.GoType.PointerType Revision.ty) (m := go!"GreaterThan")]
  wp_call
  wp_auto
  wp_apply (hGT _ (mvcc.revVal r))
  rw [show (mvcc.revOf { Main' := c + W64 1, Sub' := 0 }).gt (mvcc.revOf (mvcc.revVal r)) =
      decide (sint.Z r.main ≤ sint.Z c) from Hlo]
  by_cases Hl : sint.Z r.main ≤ sint.Z c
  · simp only [Hl, decide_true]
    wp_auto
    wp_apply (wp_map_lookup2 Revision.ty (go.GoType.StructType []) keep A (mvcc.revVal r) dq)
      $$ [$Hkeep] as Hkeep
    by_cases Hkp : (A !! mvcc.revVal r).isSome = true
    rotate_left
    · simp only [Hkp, decide_false, Bool.not_false]
      wp_auto
      rw [mvcc.hashIncl_decide c rev _ r _ Hu]
      have Hkp' : ¬ mvcc.keptBy A r := Hkp
      have Hl' : ¬ sint.Z c < sint.Z r.main := by omega
      simp only [Hl', Hkp', decide_false, Bool.or_false, Bool.false_and]
      iapply HΦ
      iframe
    simp only [Hkp, decide_true, Bool.not_true]
    wp_auto
    have HKP : (decide (sint.Z c < sint.Z r.main) || decide (mvcc.keptBy A r)) = true := by
      have : mvcc.keptBy A r := Hkp
      simp [this]
    by_cases Hmc : r.main = c
    · rw [decide_eq_true Hmc]
      wp_auto
      by_cases Ht : rest = [mvcc.markTomb]
      · rw [decide_eq_true Ht]
        wp_auto
        rw [mvcc.hashIncl_decide c rev _ r _ Hu, HKP]
        simp only [decide_eq_true Hmc, decide_eq_true Ht, Bool.true_and, Bool.and_true, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false]
        iapply HΦ
        iframe
      · rw [decide_eq_false Ht]
        wp_auto
        rw [mvcc.hashIncl_decide c rev _ r _ Hu, HKP]
        simp only [decide_eq_true Hmc, decide_eq_false Ht, Bool.true_and, Bool.and_true, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false]
        iapply HΦ
        iframe
    · rw [decide_eq_false Hmc]
      wp_auto
      rw [mvcc.hashIncl_decide c rev _ r _ Hu, HKP]
      simp only [decide_eq_false Hmc, Bool.true_and, Bool.and_true, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false]
      iapply HΦ
      iframe
  · simp only [Hl, decide_false]
    wp_auto
    have HKP : (decide (sint.Z c < sint.Z r.main) || decide (mvcc.keptBy A r)) = true := by
      have : sint.Z c < sint.Z r.main := by omega
      simp [this]
    by_cases Hmc : r.main = c
    · rw [decide_eq_true Hmc]
      wp_auto
      by_cases Ht : rest = [mvcc.markTomb]
      · rw [decide_eq_true Ht]
        wp_auto
        rw [mvcc.hashIncl_decide c rev _ r _ Hu, HKP]
        simp only [decide_eq_true Hmc, decide_eq_true Ht, Bool.true_and, Bool.and_true, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false]
        iapply HΦ
        iframe
      · rw [decide_eq_false Ht]
        wp_auto
        rw [mvcc.hashIncl_decide c rev _ r _ Hu, HKP]
        simp only [decide_eq_true Hmc, decide_eq_false Ht, Bool.true_and, Bool.and_true, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false]
        iapply HΦ
        iframe
    · rw [decide_eq_false Hmc]
      wp_auto
      rw [mvcc.hashIncl_decide c rev _ r _ Hu, HKP]
      simp only [decide_eq_false Hmc, Bool.true_and, Bool.and_true, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false]
      iapply HΦ
      iframe

end proof

end EtcdGrove
end Perennial
