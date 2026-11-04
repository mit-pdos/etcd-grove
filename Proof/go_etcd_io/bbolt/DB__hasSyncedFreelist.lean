/-
The proof of `Spec/go_etcd_io/bbolt/DB__hasSyncedFreelist.lean`: U4 (`notes/bbolt-proof-plan.md`), over `DB.meta` and `Meta.Freelist`.
-/
module

public import Spec.go_etcd_io.bbolt.DB__hasSyncedFreelist
public import Spec.go_etcd_io.bbolt.DB__meta
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Freelist
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

omit hos in
theorem DB.hasSyncedFreelist.wp_proof (hmeta : DB.meta.spec (GF := GF) (hG := hG))
    (hFreelist : internal.common.Meta.Freelist.spec (GF := GF) (hG := hG)) :
    DB.hasSyncedFreelist.spec (GF := GF) (hG := hG) := by
  intro db b l C dq q hok
  wp_start as ⟨Hmf, Hmc⟩
  wp_auto
  wp_apply hmeta db b l C dq q hok $$ [Hmf Hmc] as ⟨Hmf, Hmc⟩
  · iframe
  obtain ⟨hl0, hl1, -, -, -, -, ⟨-, -, -, hfl⟩, -⟩ := hok
  have hdec : ∀ v : Meta, metaFlpg v = C.flpg →
      (!decide (v.freelist' = W64 18446744073709551615)) = decide (C.flpg ≠ none) := by
    intro v hv
    rw [← hv]; unfold metaFlpg pgidNoFreelist
    have key : v.freelist' = W64 18446744073709551615 ↔ v.freelist'.toNat = 2 ^ 64 - 1 :=
      ⟨fun e => by rw [e]; rfl, fun e => BitVec.eq_of_toNat_eq (by rw [e]; rfl)⟩
    by_cases h2 : v.freelist'.toNat = 2 ^ 64 - 1
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h2)]
      simp [key.2 h2]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h2)]
      have h1 : ¬ v.freelist' = W64 18446744073709551615 := fun e => h2 (key.1 e)
      simp only [h1, decide_false, Bool.not_false, ne_eq, reduceCtorEq, not_false_eq_true,
        decide_true]
  simp only [mapFields, metaCellsQ]
  icases Hmc with ⟨H0, H1⟩
  rcases Nat.mod_two_eq_zero_or_one C.txid with hT | hT
  · unfold CommitSt.slot at hfl
    simp only [hT, ↓reduceIte] at hfl
    rw [show ((16 + 4096 * (C.txid % 2) : Nat) : Int) = ((16 : Nat) : Int) by simp [hT]]
    ihave %Hp0 := bytesPointsto_pos _ _ _ (by intro h; rw [h] at hl0; simp at hl0) $$ H0
    icases bytesPointsto_view_read (V := Meta) b (DFrac.own q) C.m0 16 _ rfl (by omega) Hp0
      $$ H0 with ⟨M0, C0⟩
    rw [show (decode ((C.m0.drop 16).take 64) : Meta) = metaOf C.m0 from rfl]
    generalize metaOf C.m0 = v0 at hfl ⊢
    wp_apply hFreelist _ v0 (DFrac.own q) $$ [M0] as M0
    · iframe
    try wp_auto
    rw [hdec _ hfl]
    ihave H0 := C0 $$ M0
    iapply HΦ; iframe
  · unfold CommitSt.slot at hfl
    simp only [show C.txid % 2 ≠ 0 by omega, ↓reduceIte] at hfl
    rw [show ((16 + 4096 * (C.txid % 2) : Nat) : Int) = (4096 : Int) + ((16 : Nat) : Int) by
      simp [hT], ← loc_add_assoc]
    ihave %Hp1 := bytesPointsto_pos _ _ _ (by intro h; rw [h] at hl1; simp at hl1) $$ H1
    icases bytesPointsto_view_read (V := Meta) (b +ₗ (4096 : Int)) (DFrac.own q) C.m1 16 _ rfl
      (by omega) Hp1 $$ H1 with ⟨M1, C1⟩
    rw [show (decode ((C.m1.drop 16).take 64) : Meta) = metaOf C.m1 from rfl]
    generalize metaOf C.m1 = v1 at hfl ⊢
    wp_apply hFreelist _ v1 (DFrac.own q) $$ [M1] as M1
    · iframe
    try wp_auto
    rw [hdec _ hfl]
    ihave H1 := C1 $$ M1
    iapply HΦ; iframe

end proof

end bbolt
end EtcdGrove
end Perennial
