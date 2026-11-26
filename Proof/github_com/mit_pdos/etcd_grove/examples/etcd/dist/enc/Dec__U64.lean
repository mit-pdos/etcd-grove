/-
The proof of `Dec.U64` (`Spec/.../dist/enc/Dec__U64.lean`): fewer than 8 bytes clear the flag; otherwise the
or-loop over the first 8 (the invariant: `leToU64` of the first `j`, `leToU64_take_succ`), which are
the encoding of the result (`leToU64_le`), and the rest kept (`ownSlice_slice`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Dec__U64
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Lemmas

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

theorem Dec.U64.wp_proof : Dec.U64.spec (GF := GF) (hG := hG) := by
  intro d bs ok
  wp_start as Hd
  unfold ownDec
  icases Hd with ⟨%s, %dq, Hd, Hs⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hs
  wp_auto
  wp_if_destruct
  · try wp_auto
    iapply HΦ
    unfold decPost
    iright
    iexists bs
    unfold ownDec
    iexists s, dq
    iframe
  · have hb8 : 8 ≤ bs.length := by
      have h8 : uint.Z (W64 8) = 8 := by decide
      have : sint.nat s.len = (sint.Z s.len).toNat := rfl
      have : uint.Z s.len = sint.Z s.len := by word
      omega
    clear Hif
    try wp_auto
    ihave HI : (∃ (j : w64), "i" ∷ i_ptr ↦ j ∗
        "x" ∷ x_ptr ↦ leToU64 (bs.take (uint.nat j)) ∗
        "%Hj" ∷ ⌜uint.nat j ≤ 8⌝ : IProp GF) $$ [i x]
    · iexists W64 0
      iframe
      ipureintro; simp
    wp_for HI
    wp_if_destruct
    · have hj8 : uint.nat j < 8 := by word
      clear Hif
      have hsl : sint.nat s.len = (sint.Z s.len).toNat := rfl
      have hs : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s.len := by word
      rw [ite_eq_left hs]
      have hsn : (sint.Z j).toNat = uint.nat j := by word
      obtain ⟨w, hw⟩ : ∃ w, bs[uint.nat j]? = some w :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      wp_apply wp_load_slice_index s (sint.Z j) _ dq w (by word) $$ [Hs] as Hs
      · iframe Hs; ipureintro; rw [hsn]; exact hw
      wp_for_post
      iframe
      iexists j + W64 1
      rw [show uint.nat (j + W64 1) = uint.nat j + 1 by word, leToU64_take_succ bs j w hj8 hw]
      iframe
      ipureintro; word
    · have hj8 : uint.nat j = 8 := by
        have h8 : uint.Z (W64 8) = 8 := by decide
        have hz : uint.Z j = (uint.nat j : Int) := by simp [uint.Z, uint.nat]
        omega
      clear Hif
      have hb : 0 ≤ sint.Z (W64 8) ∧ sint.Z (W64 8) ≤ sint.Z s.len ∧ sint.Z s.len ≤ sint.Z s.cap := by
        have : sint.nat s.len = (sint.Z s.len).toNat := rfl
        have : sint.Z (W64 8) = 8 := by decide
        omega
      rw [ite_eq_left hb]
      icases (ownSlice_slice (W64 8) s.len s dq bs ⟨hb.1, hb.2.1, Int.le_refl _⟩).1 $$ Hs
        with ⟨-, Hs, -⟩
      try wp_auto
      have hsub : subslice (sint.nat (W64 8)) (sint.nat s.len) bs = bs.drop 8 := by
        rw [show sint.nat (W64 8) = 8 by decide, ← Hl.1, subslice,
          List.take_of_length_le (by omega)]
      rw [hsub, hj8]
      iapply HΦ
      unfold decPost ownDec
      cases ok
      · iright
        iexists bs.drop 8, slice.slice s w8 (W64 8) s.len, dq
        iframe
      · ileft
        iexists bs.drop 8
        isplitr
        · ipureintro
          refine ⟨rfl, ?_⟩
          rw [encU64, leToU64_le _ (by simp; omega), List.take_append_drop]
        iexists slice.slice s w8 (W64 8) s.len, dq
        iframe

end proof

end github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc
end Perennial
