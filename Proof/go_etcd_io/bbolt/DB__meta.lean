/-
The proof of `Spec/go_etcd_io/bbolt/DB__meta.lean`: U4 (`notes/bbolt-proof-plan.md`), over `Meta.Txid` and `Meta.Validate`.
-/
module

public import Spec.go_etcd_io.bbolt.DB__meta
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Txid
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Validate
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

omit hos in
theorem DB.meta.wp_proof (hTxid : internal.common.Meta.Txid.spec (GF := GF) (hG := hG))
    (hValidate : internal.common.Meta.Validate.spec (GF := GF) (hG := hG)) :
    DB.meta.spec (GF := GF) (hG := hG) := by
  intro db b l C dq q hok
  obtain ⟨hl0, hl1, -, -, -, hv, ⟨ht, -⟩, hother⟩ := hok
  have key : (C.txid % 2 = 0 ∧ metaValid (metaOf C.m0) ∧ (metaOf C.m0).txid'.toNat = C.txid ∧
        (metaValid (metaOf C.m1) → (metaOf C.m1).txid'.toNat < C.txid)) ∨
      (C.txid % 2 = 1 ∧ metaValid (metaOf C.m1) ∧ (metaOf C.m1).txid'.toNat = C.txid ∧
        (metaValid (metaOf C.m0) → (metaOf C.m0).txid'.toNat < C.txid)) := by
    unfold CommitSt.slot at hv ht hother
    rcases Nat.mod_two_eq_zero_or_one C.txid with h | h
    · have h1 : (C.txid + 1) % 2 ≠ 0 := by omega
      simp only [h, h1, ↓reduceIte] at hv ht hother
      exact Or.inl ⟨h, hv, ht, hother⟩
    · have h0 : C.txid % 2 ≠ 0 := by omega
      have h1 : (C.txid + 1) % 2 = 0 := by omega
      simp only [h0, h1, ↓reduceIte] at hv ht hother
      exact Or.inr ⟨h, hv, ht, hother⟩
  clear hv ht hother
  wp_start as ⟨Hmf, Hmc⟩
  simp only [mapFields, metaCellsQ]
  icases Hmf with ⟨Hdr, Hd, H0f, H1f, %Hpure⟩
  icases Hmc with ⟨H0, H1⟩
  ihave %Hp0 := bytesPointsto_pos _ _ _ (by intro h; rw [h] at hl0; simp at hl0) $$ H0
  ihave %Hp1 := bytesPointsto_pos _ _ _ (by intro h; rw [h] at hl1; simp at hl1) $$ H1
  have e0 : b +ₗ (16 : Int) = b +ₗ ((16 : Nat) : Int) := by simp
  have e1 : b +ₗ (4112 : Int) = (b +ₗ (4096 : Int)) +ₗ ((16 : Nat) : Int) := by
    rw [loc_add_assoc]; rfl
  have hp1 : 0 < (b +ₗ (4096 : Int)).addr := Hp1
  have hl0' : 16 + 64 ≤ C.m0.length := by omega
  have hl1' : 16 + 64 ≤ C.m1.length := by omega
  icases bytesPointsto_view_read (V := Meta) b (DFrac.own q) C.m0 16 _ e0 hl0' Hp0 $$ H0
    with ⟨M0, C0⟩
  icases bytesPointsto_view_read (V := Meta) _ (DFrac.own q) C.m1 16 _ e1 hl1' hp1 $$ H1
    with ⟨M1, C1⟩
  rw [show (decode ((C.m0.drop 16).take 64) : Meta) = metaOf C.m0 from rfl,
    show (decode ((C.m1.drop 16).take 64) : Meta) = metaOf C.m1 from rfl]
  generalize metaOf C.m0 = v0 at key ⊢
  generalize metaOf C.m1 = v1 at key ⊢
  wp_auto
  wp_apply hTxid _ v1 (DFrac.own q) $$ [M1] as M1
  · iframe
  try wp_auto
  wp_apply hTxid _ v0 (DFrac.own q) $$ [M0] as M0
  · iframe
  try wp_auto
  have hpA : 0 < (b +ₗ (16 : Int)).addr := by simp only [Loc.add]; omega
  have hpB : 0 < (b +ₗ (4112 : Int)).addr := by simp only [Loc.add]; omega
  by_cases hc : uint.Z v0.txid' < uint.Z v1.txid'
  · rw [decide_eq_true hc]
    wp_auto
    rcases key with ⟨hT, hv0, ht0, hv1⟩ | ⟨hT, hv1, ht1, hv0⟩
    · have hn1 : ¬ metaValid v1 := fun h => by have := hv1 h; word
      wp_apply hValidate _ v1 (DFrac.own q) hpB $$ [M1] as %e ⟨M1, %He⟩
      · iframe
      have hne : e ≠ GoInterface.nil := fun h => hn1 (He.1 h)
      try wp_auto
      cases e with
      | nil => exact absurd rfl hne
      | ok i =>
        wp_auto
        wp_apply hValidate _ v0 (DFrac.own q) hpA $$ [M0] as %e ⟨M0, %He⟩
        · iframe
        have he : e = GoInterface.nil := He.2 hv0
        subst he
        wp_auto
        rw [show ((16 + 4096 * (C.txid % 2) : Nat) : Int) = 16 by simp [hT]]
        ihave H0 := C0 $$ M0
        ihave H1 := C1 $$ M1
        iapply HΦ
        iframe
        ipureintro; exact Hpure
    · wp_apply hValidate _ v1 (DFrac.own q) hpB $$ [M1] as %e ⟨M1, %He⟩
      · iframe
      have he : e = GoInterface.nil := He.2 hv1
      subst he
      wp_auto
      rw [show ((16 + 4096 * (C.txid % 2) : Nat) : Int) = 4112 by simp [hT]]
      ihave H0 := C0 $$ M0
      ihave H1 := C1 $$ M1
      iapply HΦ
      iframe
      ipureintro; exact Hpure
  · rw [decide_eq_false hc]
    wp_auto
    rcases key with ⟨hT, hv0, ht0, hv1⟩ | ⟨hT, hv1, ht1, hv0⟩
    · wp_apply hValidate _ v0 (DFrac.own q) hpA $$ [M0] as %e ⟨M0, %He⟩
      · iframe
      have he : e = GoInterface.nil := He.2 hv0
      subst he
      wp_auto
      rw [show ((16 + 4096 * (C.txid % 2) : Nat) : Int) = 16 by simp [hT]]
      ihave H0 := C0 $$ M0
      ihave H1 := C1 $$ M1
      iapply HΦ
      iframe
      ipureintro; exact Hpure
    · have hn0 : ¬ metaValid v0 := fun h => by have := hv0 h; word
      wp_apply hValidate _ v0 (DFrac.own q) hpA $$ [M0] as %e ⟨M0, %He⟩
      · iframe
      have hne : e ≠ GoInterface.nil := fun h => hn0 (He.1 h)
      try wp_auto
      cases e with
      | nil => exact absurd rfl hne
      | ok i =>
        wp_auto
        wp_apply hValidate _ v1 (DFrac.own q) hpB $$ [M1] as %e ⟨M1, %He⟩
        · iframe
        have he : e = GoInterface.nil := He.2 hv1
        subst he
        wp_auto
        rw [show ((16 + 4096 * (C.txid % 2) : Nat) : Int) = 4112 by simp [hT]]
        ihave H0 := C0 $$ M0
        ihave H1 := C1 $$ M1
        iapply HΦ
        iframe
        ipureintro; exact Hpure

end proof

end bbolt
end EtcdGrove
end Perennial
