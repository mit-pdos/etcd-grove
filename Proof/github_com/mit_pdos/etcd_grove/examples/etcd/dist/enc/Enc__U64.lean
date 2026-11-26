/-
The proof of `Enc.U64` (`Spec/.../dist/enc/Enc__U64.lean`): eight appends of one byte each; the
invariant holds `u64Le x`'s first `j` bytes after `bs`, byte `j` being `byte(x >> (8*j))`
(`u64Le_getElem`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Enc__U64
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

theorem Enc.U64.wp_proof : Enc.U64.spec (GF := GF) (hG := hG) := by
  intro e bs x
  wp_start as He
  unfold ownEnc
  icases He with ⟨%s, He, Hs, Hcap⟩
  wp_auto
  ihave HI : (∃ (j : w64) (s : GoSlice), "i" ∷ i_ptr ↦ j ∗ "He" ∷ e ↦ ({ B' := s } : Enc) ∗
      "Hs" ∷ s ↦* (bs ++ (u64Le x).take (uint.nat j)) ∗
      "Hcap" ∷ ownSliceCap w8 s (DFrac.own 1) ∗ "%Hj" ∷ ⌜uint.nat j ≤ 8⌝ : IProp GF)
      $$ [i He Hs Hcap]
  · iexists W64 0, s
    simp only [show uint.nat (W64 0) = 0 from rfl, List.take_zero, List.append_nil]
    iframe
    ipureintro; omega
  wp_for HI
  wp_if_destruct
  · have hj8 : uint.nat j < 8 := by word
    clear Hif
    wp_apply wp_slice_literal (V := w8) [_]
    isplitr
    · ipureintro; rfl
    iintro %lit ⟨Hlit, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [$Hs $Hcap $Hlit] as %s' ⟨Hs, Hcap, -⟩
    try wp_auto
    wp_for_post
    iframe
    iexists j + W64 1, s'
    rw [show uint.nat (j + W64 1) = uint.nat j + 1 by word, List.take_add_one,
      u64Le_getElem x j hj8]
    simp only [Option.toList_some, List.append_assoc]
    iframe
    ipureintro; word
  · have hj8 : uint.nat j = 8 := by
      have h8 : uint.Z (W64 8) = 8 := by decide
      have hz : uint.Z j = (uint.nat j : Int) := by simp [uint.Z, uint.nat]
      omega
    clear Hif
    rw [hj8, List.take_of_length_le (by simp [u64Le_length])]
    try wp_auto
    iapply HΦ
    iexists s
    iframe

end proof

end github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc
end Perennial
