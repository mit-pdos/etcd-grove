/-
`DB.mmapSize` (U4, `notes/bbolt-proof-plan.md`): the mapping size for a database of `size`
bytes. Proved: the `for` loop over `i ∈ [15, 30]` (`mmapSizeOf_pow`), then, above 1 GiB, the
`int64` rounding to a GiB (`mmapSize_round`; the page rounding is a no-op, `srem4096_zero`) and
the cap; the `errors.New` error is `fmtErrorOk` (`errorString_fmtErrorOk`, `Proof/errors/ErrorStringOk`).

Note: above 1 GiB the size is rounded up to a whole GiB and then capped at `MaxMapSize`
(`0xFFFFFFFFFFFF`), which is not a multiple of 4096: a mapping need not end on a page
(`mmapSizeOf` below), so an invariant `l % 4096 = 0` on the mapping's length is false for sizes
in `(2^48 - 2^30, 2^48 - 1]` (U4 finding).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Locks
public import Proof.go_etcd_io.bbolt.PkgInit
public import Spec.fmt.ErrorOk
public import Proof.errors.ErrorStringOk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

/-- `DB.mmapSize`'s result for `size` (page size 4096): the least power of two from 32 KiB to
1 GiB at least `size`; above that `size` rounded up to a whole GiB, at most `MaxMapSize`; `none`
(an error) above `MaxMapSize`. -/
def mmapSizeOf (size : Nat) : Option Nat :=
  match (List.range 16).find? (fun i => decide (size ≤ 2 ^ (15 + i))) with
  | some i => some (2 ^ (15 + i))
  | none =>
    if size > 0xFFFFFFFFFFFF then none
    else some (min (if size % 0x40000000 > 0 then size + 0x40000000 - size % 0x40000000 else size)
      0xFFFFFFFFFFFF)

theorem mmapSizeOf_pow (size j : Nat) (hj1 : 15 ≤ j) (hj2 : j ≤ 30) (hle : size ≤ 2 ^ j)
    (hlt : ∀ k, 15 ≤ k → k < j → 2 ^ k < size) : mmapSizeOf size = some (2 ^ j) := by
  unfold mmapSizeOf
  have : (List.range 16).find? (fun i => decide (size ≤ 2 ^ (15 + i))) = some (j - 15) := by
    rw [List.find?_eq_some_iff_getElem]
    have hjj : 15 + (j - 15) = j := by omega
    refine ⟨by rw [hjj]; simpa using hle, j - 15, by simp; omega, by simp, fun i hi => ?_⟩
    have := hlt (15 + i) (by omega) (by omega)
    simp; omega
  rw [this]; simp only; congr 2; omega

theorem shl_one_w64 (j : w64) (hj : j.toNat ≤ 30) :
    sint.Z (W64 1 <<< j) = 2 ^ j.toNat := by
  have h1 : (W64 1 <<< j).toNat = 2 ^ j.toNat := by
    rw [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft]
    have : (2 : Nat) ^ j.toNat < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega)
    have h30 : (2 : Nat) ^ j.toNat ≤ 2 ^ 30 := Nat.pow_le_pow_right (by decide) hj
    simp [Nat.shiftLeft_eq]
    omega
  have h30 : (2 : Nat) ^ j.toNat ≤ 2 ^ 30 := Nat.pow_le_pow_right (by decide) hj
  rw [sint.Z, BitVec.toInt_eq_toNat_cond, h1]
  have : 2 * 2 ^ j.toNat < 2 ^ 64 := by omega
  simp [this]

theorem two_pow_cast (n : Nat) : (((2 : Nat) ^ n : Nat) : Int) = (2 : Int) ^ n := by
  push_cast; rfl

theorem toNat_le_pow (a : Int) (n : Nat) (h : a ≤ (2 : Int) ^ n) : a.toNat ≤ 2 ^ n := by
  rw [← two_pow_cast] at h; generalize (2 : Nat) ^ n = p at h ⊢; omega

theorem pow_lt_toNat (a : Int) (n : Nat) (h : ¬ a ≤ (2 : Int) ^ n) : 2 ^ n < a.toNat := by
  rw [← two_pow_cast] at h; generalize (2 : Nat) ^ n = p at h ⊢; omega

theorem int_two_pow_toNat (n : Nat) : ((2 : Int) ^ n).toNat = 2 ^ n := by
  rw [← two_pow_cast]; generalize (2 : Nat) ^ n = p; omega

theorem srem4096_zero (v : w64) (h0 : 0 ≤ sint.Z v) (hd : sint.Z v % 4096 = 0) :
    BitVec.srem v (W64 4096) = W64 0 := by
  apply BitVec.toInt_inj.mp
  rw [BitVec.toInt_srem, Int.tmod_eq_emod_of_nonneg h0]
  exact hd

/-- The rounded size, capped: what is left of `DB.mmapSize` past the loop. -/
theorem mmapSize_round (S R : Int) (hS : 2 ^ 30 < S ∧ S ≤ 281474976710655)
    (hR : R = if S % 1073741824 > 0 then S + 1073741824 - S % 1073741824 else S) :
    (if S.toNat % 1073741824 > 0 then S.toNat + 1073741824 - S.toNat % 1073741824
      else S.toNat) = R.toNat ∧ R ≤ 281474976710656 ∧ 0 ≤ R ∧ R % 4096 = 0 := by
  subst hR
  split <;> split <;> omega

theorem mmapSizeOf_big (size : Nat) (h : 2 ^ 30 < size) :
    mmapSizeOf size = if size > 0xFFFFFFFFFFFF then none
    else some (min (if size % 0x40000000 > 0 then size + 0x40000000 - size % 0x40000000 else size)
      0xFFFFFFFFFFFF) := by
  unfold mmapSizeOf
  have : (List.range 16).find? (fun i => decide (size ≤ 2 ^ (15 + i))) = none := by
    rw [List.find?_eq_none]
    intro i hi
    simp at hi ⊢
    have : 2 ^ (15 + i) ≤ 2 ^ 30 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  rw [this]

section msz
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`db.mmapSize(size)`**: `mmapSizeOf size`, or an `errors.New` error. -/
abbrev DB.mmapSize.spec : Prop :=
  ∀ (db : Loc) (size : w64),
  0 ≤ sint.Z size →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ db.[DB, go!"pageSize"] ↦□ W64 4096 }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"mmapSize")) (Val #size))
  {{ (r : w64) (err : GoInterface), RET (PairV #r #err);
      match mmapSizeOf (sint.nat size) with
      | some s => ⌜err = interface.nil ∧ sint.nat r = s⌝
      | none => ⌜err ≠ interface.nil⌝ ∗ fmtErrorOk err }}

theorem DB.mmapSize.wp_proof : DB.mmapSize.spec (GF := GF) (hG := hG) := by
  intro db size hsz
  wp_start as #Hps
  wp_auto
  ihave IH : (∃ (j : w64), "i" ∷ i_ptr ↦ j ∗
      "%Hj" ∷ ⌜15 ≤ j.toNat ∧ j.toNat ≤ 31 ∧ ∀ k, 15 ≤ k → k < j.toNat → 2 ^ k < sint.nat size⌝ :
      IProp GF) $$ [i]
  · iexists W64 15
    simp only [named]
    iframe
    ipureintro; refine ⟨by decide, by decide, fun k h1 h2 => ?_⟩; simp at h2; omega
  wp_for IH
  wp_if_destruct
  · try wp_auto
    have hj30 : j.toNat ≤ 30 := by word
    have hshl := shl_one_w64 j hj30
    wp_if_destruct
    · try wp_auto
      wp_for_post
      iapply HΦ
      rw [mmapSizeOf_pow (sint.nat size) j.toNat Hj.1 hj30 (by rw [hshl] at Hif; exact toNat_le_pow _ _ Hif) Hj.2.2]
      ipureintro
      refine ⟨rfl, ?_⟩
      rw [show sint.nat (W64 1 <<< j) = (sint.Z (W64 1 <<< j)).toNat from rfl, hshl, int_two_pow_toNat]
    · try wp_auto
      wp_for_post
      iframe
      iexists j + W64 1
      iframe
      ipureintro
      have hjn : (j + W64 1).toNat = j.toNat + 1 := by word
      rw [hjn]
      refine ⟨by omega, by omega, fun k h1 h2 => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h | h
      · exact Hj.2.2 k h1 h
      · subst h; rw [hshl] at Hif; exact pow_lt_toNat _ _ Hif
  · have hj31 : j.toNat = 31 := by word
    have hbig : 2 ^ 30 < sint.nat size := Hj.2.2 30 (by decide) (by omega)
    try wp_auto
    rw [mmapSizeOf_big _ hbig]
    wp_if_destruct
    · wp_apply errors.wp_New_errorString as %x #Hx
      try wp_auto
      iapply HΦ
      have hgt : sint.nat size > 0xFFFFFFFFFFFF := by word
      simp only [hgt, ↓reduceIte]
      isplitr
      · ipureintro; exact fun h => nomatch h
      · iapply errorString_fmtErrorOk $$ Hx
    · have hle : ¬ sint.nat size > 0xFFFFFFFFFFFF := by word
      simp only [hle, ↓reduceIte]
      have hS : 2 ^ 30 < sint.Z size ∧ sint.Z size ≤ 281474976710655 := by
        rw [show sint.nat size = (sint.Z size).toNat from rfl] at hbig hle; omega
      have hrem : sint.Z (BitVec.srem size (W64 1073741824)) = sint.Z size % 1073741824 := by
        show (BitVec.srem size _).toInt = size.toInt % _
        rw [BitVec.toInt_srem, Int.tmod_eq_emod_of_nonneg hsz]; rfl
      rw [hrem]
      try wp_auto
      wp_if_destruct
      · try wp_auto
        have hv : sint.Z (size + (W64 1073741824 - BitVec.srem size (W64 1073741824))) =
            sint.Z size + 1073741824 - sint.Z size % 1073741824 := by
          have h0 : 0 ≤ sint.Z size % 1073741824 := Int.emod_nonneg _ (by decide)
          have h1 : sint.Z size % 1073741824 < 1073741824 := Int.emod_lt_of_pos _ (by decide)
          word
        obtain ⟨hR1, hR2, hR3, hR4⟩ := mmapSize_round (sint.Z size) _ hS
          (ite_eq_left (by word : sint.Z size % 1073741824 > 0)).symm
        rw [← hv] at hR1 hR2 hR3 hR4
        generalize size + (W64 1073741824 - BitVec.srem size (W64 1073741824)) = v at *
        rw [srem4096_zero _ hR3 hR4]
        simp only [decide_true, Bool.not_true]
        try wp_auto
        rw [show sint.nat size = (sint.Z size).toNat from rfl, hR1]
        have hcap : sint.Z (W64 281474976710655) = 281474976710655 := rfl
        rw [hcap]
        wp_if_destruct
        · try wp_auto
          iapply HΦ
          ipureintro
          refine ⟨rfl, ?_⟩
          rw [show sint.nat (W64 281474976710655) = (sint.Z (W64 281474976710655)).toNat from rfl,
            hcap]
          omega
        · try wp_auto
          iapply HΦ
          ipureintro
          refine ⟨rfl, ?_⟩
          rw [show sint.nat v = (sint.Z v).toNat from rfl]
          omega
      · try wp_auto
        obtain ⟨hR1, hR2, hR3, hR4⟩ := mmapSize_round (sint.Z size) _ hS
          (ite_eq_right (by word : ¬ sint.Z size % 1073741824 > 0)).symm
        rw [srem4096_zero _ hR3 hR4]
        simp only [decide_true, Bool.not_true]
        try wp_auto
        rw [show sint.nat size = (sint.Z size).toNat from rfl, hR1]
        have hcap : sint.Z (W64 281474976710655) = 281474976710655 := rfl
        rw [hcap]
        wp_if_destruct
        · try wp_auto
          iapply HΦ
          ipureintro
          refine ⟨rfl, ?_⟩
          rw [show sint.nat (W64 281474976710655) = (sint.Z (W64 281474976710655)).toNat from rfl,
            hcap]
          omega
        · try wp_auto
          iapply HΦ
          ipureintro
          refine ⟨rfl, ?_⟩
          rw [show sint.nat size = (sint.Z size).toNat from rfl]
          omega

end msz

end bbolt
end EtcdGrove
end Perennial
