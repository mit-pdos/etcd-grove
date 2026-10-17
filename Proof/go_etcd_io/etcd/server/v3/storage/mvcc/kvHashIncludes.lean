/-
Proof of `Spec/.../mvcc/kvHashIncludes.lean` (pr-verify/etcd-22562, pr-verify/etcd-22515; without `exactKeep`, the filter at the pin as etcd-io/etcd#21202's `shouldWriteKeyValue` keeps it: pr-verify/etcd-21202).
Lean-first.
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

/-- `hashInclF` of a pair at or below the hasher's revision, as the code computes it. -/
theorem mvcc.hashInclF_decide (c rev : w64) (K : mvcc.Rev → Prop) [DecidablePred K] (f : Bool)
    (r : mvcc.Rev) (t : Bool) (Hu : sint.Z r.main ≤ sint.Z rev) :
    decide (mvcc.hashInclF (sint.Z c) (sint.Z rev) K f r t) =
      (Bool.or (Bool.or (decide (sint.Z c < sint.Z r.main)) (Bool.not f)) (decide (K r)) &&
        Bool.not (decide (r.main = c) && t)) := by
  have hiff : sint.Z r.main = sint.Z c ↔ r.main = c := ⟨fun h => by word, fun h => by rw [h]⟩
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  unfold mvcc.hashInclF
  by_cases h1 : sint.Z c < sint.Z r.main <;> by_cases h2 : K r <;> by_cases h3 : r.main = c <;>
    cases t <;> cases f <;> simp [h1, h2, h3, hiff, Hu] <;> (rw [← h3]; exact Hu)

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
  · simp only [Hu, _root_.decide_false, Bool.not_false]
    wp_auto
    have : decide (mvcc.hashInclF (sint.Z c) (sint.Z rev) (mvcc.keptBy A)
        (false || decide (0 < GMap.size A)) r (decide (rest = [mvcc.markTomb]))) = false := by
      simp [mvcc.hashInclF, Hu]
    rw [this]
    iapply HΦ
    iframe
  simp only [Hu, _root_.decide_true, Bool.not_true]
  wp_auto
  wp_apply (hB2BK s r rest dk hrest hm hsub) $$ [$Hs] as Hs
  -- `lower.GreaterThan(kr)`
  rw [method_unfold (t := go.GoType.PointerType Revision.ty) (m := go!"GreaterThan")]
  wp_call
  wp_auto
  wp_apply (hGT _ (mvcc.revVal r))
  rw [show (mvcc.revOf { Main' := c + W64 1, Sub' := 0 }).gt (mvcc.revOf (mvcc.revVal r)) =
      decide (sint.Z r.main ≤ sint.Z c) from Hlo]
  rw [mvcc.hashInclF_decide c rev _ _ r _ Hu]
  -- the tombstone check that ends every path that does not return `false` on the kept set
  have Htail : ∀ (b : Bool), b = true →
      (Bool.not (decide (r.main = c) && decide (rest = [mvcc.markTomb]))) =
        (b && Bool.not (decide (r.main = c) && decide (rest = [mvcc.markTomb]))) := by
    intro b hb; rw [hb, Bool.true_and]
  by_cases Hl : sint.Z r.main ≤ sint.Z c
  · simp only [Hl, _root_.decide_true]
    wp_auto
    · (try wp_auto)
      wp_apply wp_map_len_lt $$ Hkeep as ⟨Hkeep, %Hsz⟩
      have Hsz' : decide (sint.Z (W64 0) < sint.Z (W64 (GMap.size A : Int))) = decide (0 < GMap.size A) := by
        have h0 : sint.Z (W64 (GMap.size A : Int)) = GMap.size A := by word
        rw [h0, show sint.Z (W64 0) = 0 by decide]; simp
      rw [Hsz']
      by_cases Hne : 0 < GMap.size A
      · rw [decide_eq_true Hne]
        wp_auto
        wp_apply (wp_map_lookup2 Revision.ty (go.GoType.StructType []) keep A (mvcc.revVal r) dq)
          $$ [$Hkeep] as Hkeep
        have Hl' : ¬ sint.Z c < sint.Z r.main := by omega
        by_cases Hkp : (A !! mvcc.revVal r).isSome = true
        rotate_left
        · simp only [Hkp, _root_.decide_false, Bool.not_false]
          wp_auto
          have Hkp' : ¬ mvcc.keptBy A r := Hkp
          simp only [Hl', Hkp', Hne, _root_.decide_true, Bool.false_or, Bool.not_true, _root_.decide_false, Bool.or_false, Bool.false_or, Bool.false_and, Bool.not_true]
          iapply HΦ
          iframe
        simp only [Hkp, _root_.decide_true, Bool.not_true]
        wp_auto
        have HX : Bool.or (Bool.or (decide (sint.Z c < sint.Z r.main)) (Bool.not (false || true))) (decide (mvcc.keptBy A r)) = true := by
          have : mvcc.keptBy A r := Hkp
          simp [this]
        rw [HX, Bool.true_and]
        by_cases Hmc : r.main = c
        · rw [decide_eq_true Hmc]
          wp_auto
          by_cases Ht : rest = [mvcc.markTomb]
          · rw [decide_eq_true Ht]
            wp_auto
            try simp only [Bool.true_and, Bool.not_true, Bool.not_false]
            iapply HΦ
            iframe
          · rw [decide_eq_false Ht]
            wp_auto
            try simp only [Bool.and_false, Bool.not_true, Bool.not_false]
            iapply HΦ
            iframe
        · rw [decide_eq_false Hmc]
          wp_auto
          try simp only [Bool.false_and, Bool.not_true, Bool.not_false]
          iapply HΦ
          iframe
      · rw [decide_eq_false Hne]
        wp_auto
        have HX : Bool.or (Bool.or (decide (sint.Z c < sint.Z r.main)) (Bool.not (false || false))) (decide (mvcc.keptBy A r)) = true := by
          simp
        rw [HX, Bool.true_and]
        by_cases Hmc : r.main = c
        · rw [decide_eq_true Hmc]
          wp_auto
          by_cases Ht : rest = [mvcc.markTomb]
          · rw [decide_eq_true Ht]
            wp_auto
            try simp only [Bool.true_and, Bool.not_true, Bool.not_false]
            iapply HΦ
            iframe
          · rw [decide_eq_false Ht]
            wp_auto
            try simp only [Bool.and_false, Bool.not_true, Bool.not_false]
            iapply HΦ
            iframe
        · rw [decide_eq_false Hmc]
          wp_auto
          try simp only [Bool.false_and, Bool.not_true, Bool.not_false]
          iapply HΦ
          iframe
  · simp only [Hl, _root_.decide_false]
    wp_auto
    have HX : Bool.or (Bool.or (decide (sint.Z c < sint.Z r.main)) (Bool.not (false || decide (0 < GMap.size A)))) (decide (mvcc.keptBy A r)) = true := by
      have : sint.Z c < sint.Z r.main := by omega
      simp [this]
    rw [HX, Bool.true_and]
    by_cases Hmc : r.main = c
    · rw [decide_eq_true Hmc]
      wp_auto
      by_cases Ht : rest = [mvcc.markTomb]
      · rw [decide_eq_true Ht]
        wp_auto
        try simp only [Bool.true_and, Bool.not_true, Bool.not_false]
        iapply HΦ
        iframe
      · rw [decide_eq_false Ht]
        wp_auto
        try simp only [Bool.and_false, Bool.not_true, Bool.not_false]
        iapply HΦ
        iframe
    · rw [decide_eq_false Hmc]
      wp_auto
      try simp only [Bool.false_and, Bool.not_true, Bool.not_false]
      iapply HΦ
      iframe

end proof

end EtcdGrove
end Perennial
