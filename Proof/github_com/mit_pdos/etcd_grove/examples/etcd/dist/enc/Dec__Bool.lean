/-
The proof of `Dec.Bool` (`Spec/.../dist/enc/Dec__Bool.lean`): an empty slice or a first byte above 1 clears the
flag; otherwise the byte is the encoding of the result, and the rest is kept (`ownSlice_slice`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Dec__Bool

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Assumptions]

theorem Dec.Bool.wp_proof : Dec.Bool.spec (GF := GF) (hG := hG) := by
  intro d bs ok
  wp_start as Hd
  unfold ownDec
  icases Hd with ⟨%s, %dq, Hd, Hs⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hs
  wp_auto
  have hsl : sint.nat s.len = (sint.Z s.len).toNat := rfl
  have h1 : sint.Z (W64 1) = 1 := by decide
  have hlen : sint.Z s.len = bs.length := by omega
  clear Hl hsl
  rcases bs with _ | ⟨b, r⟩
  · -- empty: the flag cleared
    rw [show decide (sint.Z s.len < sint.Z (W64 1)) = true by simp at hlen; simp; omega]
    wp_auto
    iapply HΦ
    unfold decPost
    iright
    iexists []
    unfold ownDec
    iexists s, dq
    iframe
  · rw [show decide (sint.Z s.len < sint.Z (W64 1)) = false by simp at hlen; simp; omega]
    have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z s.len := by
      simp at hlen; have : sint.Z (W64 0) = 0 := by decide
      omega
    wp_auto
    rw [ite_eq_left h0]
    wp_apply wp_load_slice_index s (sint.Z (W64 0)) _ dq b (by decide) $$ [Hs] as Hs
    · iframe Hs; ipureintro; rfl
    by_cases hb1 : uint.Z (W8 1) < uint.Z b
    · rw [show decide (uint.Z (W8 1) < uint.Z b) = true from decide_eq_true hb1]
      wp_auto
      iapply HΦ
      unfold decPost
      iright
      iexists b :: r
      unfold ownDec
      iexists s, dq
      iframe
    · rw [show decide (uint.Z (W8 1) < uint.Z b) = false from decide_eq_false hb1]
      wp_auto
      rw [ite_eq_left h0]
      wp_apply wp_load_slice_index s (sint.Z (W64 0)) _ dq b (by decide) $$ [Hs] as Hs
      · iframe Hs; ipureintro; rfl
      have hb : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z s.len ∧ sint.Z s.len ≤ sint.Z s.cap := by
        simp at hlen; omega
      rw [ite_eq_left hb]
      icases (ownSlice_slice (W64 1) s.len s dq (b :: r) ⟨hb.1, hb.2.1, Int.le_refl _⟩).1 $$ Hs
        with ⟨-, Hs, -⟩
      try wp_auto
      have hsub : subslice (sint.nat (W64 1)) (sint.nat s.len) (b :: r) = r := by
        have : sint.nat s.len = (b :: r).length := by
          have : sint.nat s.len = (sint.Z s.len).toNat := rfl
          omega
        rw [show sint.nat (W64 1) = 1 by decide, this, subslice, List.take_length]
        rfl
      rw [hsub]
      have hb01 : b = W8 0 ∨ b = W8 1 := by
        have : b.toNat ≤ 1 := by simpa using hb1
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 this with h | h
        · left; apply BitVec.eq_of_toNat_eq; simp [h]
        · right; apply BitVec.eq_of_toNat_eq; simp [h]
      have henc : b :: r = encBool (decide (b = W8 1)) ++ r := by
        rcases hb01 with rfl | rfl <;> rfl
      iapply HΦ
      unfold decPost ownDec
      cases ok
      · iright
        iexists r, slice.slice s w8 (W64 1) s.len, dq
        iframe
      · ileft
        iexists r
        isplitr
        · ipureintro; exact ⟨rfl, henc⟩
        iexists slice.slice s w8 (W64 1) s.len, dq
        iframe

end proof

end github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc
end Perennial
