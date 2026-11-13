/-
The proof of `LinuxFs/Spec/hash/crc32/Update.lean`: the trusted model's loop (`simpleUpdate`) by
Löb induction on the slice.
-/
module

public import LinuxFs.Spec.hash.crc32.Update

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [hash.crc32.Assumptions]

theorem hash.crc32.Update.wp_proof : hash.crc32.Update.spec (GF := GF) (hG := hG) := by
  intro c tab s bs dq
  wp_start as ⟨#Ht, Hs⟩
  unfold hash.crc32.crc32c hash.crc32.crcUpdate
  generalize ~~~c = c0
  iloeb as IH generalizing %c0 %s %bs Hs HΦ
  icases ownSlice_len s _ bs $$ Hs with %Hlen
  icases ownSlice_wf s _ bs $$ Hs with %Hwf
  cases bs with
  | nil =>
    have h0 : s.len = W64 0 := by
      simp only [List.length_nil, sint.nat, sint.Z] at Hlen; apply BitVec.eq_of_toInt_eq; simp; omega
    rw [decide_eq_true h0]
    wp_auto
    rw [List.foldl_nil]
    iapply HΦ
    iexact Hs
  | cons b bs =>
    have h0 : ¬ s.len = W64 0 := by
      intro h; rw [h] at Hlen; simp [sint.nat, sint.Z] at Hlen
    rw [decide_eq_false h0]
    have hz : sint.Z (W64 0) = 0 := rfl
    have hlen1 : 1 ≤ sint.Z s.len := by
      simp only [List.length_cons, sint.nat, sint.Z] at Hlen ⊢; omega
    wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true (⟨by rw [hz]; exact Int.le_refl 0, by rw [hz]; omega⟩ :
      0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z s.len))]
    wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ _ b (by rw [hz]; exact Int.le_refl 0) $$ [Hs] with Hs
    · iframe; ipureintro; rfl
    obtain ⟨k, hk⟩ : ∃ k : Nat, k = (W8 (uint.Z c0) ^^^ b).toNat := ⟨_, rfl⟩
    have hk256 : k < 256 := by rw [hk]; exact BitVec.isLt _
    have hi : sint.Z (W64 (uint.Z (W8 (uint.Z c0) ^^^ b))) = k := by
      rw [hk]; word
    rw [hi, ite_eq_left_of_eq_true _ _ (eq_true (⟨by omega, by omega⟩ : (0 : Int) ≤ k ∧ (k : Int) < 256))]
    have hlk : hash.crc32.castagnoliTableArr.arr[(k : Int).toNat]? =
        some (hash.crc32.crcTableEntry hash.crc32.castagnoliPoly k) := by
      simp [hash.crc32.castagnoliTableArr, hash.crc32.crcTableOf, hk256]
    icases array_acc tab k _ 256 _ _ (by omega) hlk $$ Ht with ⟨He, -⟩
    wp_auto
    have h1 : sint.Z (W64 1) = 1 := rfl
    rw [ite_eq_left_of_eq_true _ _ (eq_true (⟨by rw [h1]; omega, by rw [h1]; omega, Hwf.2⟩ :
      0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z s.len ∧ sint.Z s.len ≤ sint.Z s.cap))]
    icases (ownSlice_split_all (W64 1) s dq (b :: bs) ⟨by rw [h1]; omega, by rw [h1]; omega⟩).1 $$ Hs
      with ⟨H0, H1⟩
    have hs1 : sint.nat (W64 1) = 1 := rfl
    rw [hs1, List.drop_one, List.tail_cons]
    wp_auto
    have hsl : (slice.slice s w8 (W64 1) s.len).len = s.len - W64 1 := by
      simp [slice.slice]
    rw [← hsl]
    iapply IH $$ %(hash.crc32.crcTableEntry hash.crc32.castagnoliPoly k ^^^ c0 >>> W64 8)
      %(slice.slice s w8 (W64 1) s.len) %bs [H1]
    · iexact H1
    iintro H1
    have hstep : hash.crc32.crcUpdByte (hash.crc32.crcTableOf hash.crc32.castagnoliPoly) c0 b =
        hash.crc32.crcTableEntry hash.crc32.castagnoliPoly k ^^^ c0 >>> W64 8 := by
      have hw : W8 (uint.Z c0) = BitVec.ofNat 8 c0.toNat := by word
      have hs8 : c0 >>> W64 8 = c0 >>> 8 := rfl
      simp only [hash.crc32.crcUpdByte, hash.crc32.crcTableOf, hk, hw, hs8, List.getD_eq_getElem?_getD,
        List.getElem?_map, List.getElem?_range (show (BitVec.ofNat 8 c0.toNat ^^^ b).toNat < 256 from
          BitVec.isLt _), Option.map_some, Option.getD_some]
    rw [List.foldl_cons, hstep]
    iapply HΦ
    ihave Hc := ownSlice_combine (W64 1) s dq (List.take 1 (b :: bs)) bs (W64 0) s.len
      ⟨by simp; rfl, by rw [hz]; exact Int.le_refl 0, by rw [hz, h1]; omega, by rw [h1]; omega⟩ $$ H0 H1
    rw [List.take_one, List.head?_cons, Option.toList_some, List.singleton_append,
      ← slice_slice_trivial]
    iexact Hc

end proof

end EtcdGrove
end Perennial
