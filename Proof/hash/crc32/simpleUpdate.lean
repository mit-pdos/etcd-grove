/-
The proof of `Spec/hash/crc32/simpleUpdate.lean`: the range loop, byte by byte.
-/
module

public import Spec.hash.crc32.simpleUpdate

@[expose] public section

set_option linter.unusedSectionVars false

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

theorem hash.crc32.simpleUpdate.wp_proof : hash.crc32.simpleUpdate.spec (GF := GF) (hG := hG) := by
  intro c tab dt ta s bs dq
  wp_start as ⟨Ht, Hs⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  icases array_len _ _ _ _ $$ Ht with %Hal
  wp_auto
  ihave IH : iprop(∃ (n : Nat),
      "i" ∷ i_ptr ↦ W64 (n : Int) ∗
      "crc" ∷ crc_ptr ↦ (bs.take n).foldl (hash.crc32.crcUpdByte ta.arr) (~~~c) ∗
      "v" ∷ (∃ y : w8, v_ptr ↦ y) ∗
      "%Hn" ∷ ⌜n ≤ bs.length⌝) $$ [i crc v]
  · iexists 0
    iframe
    isplitl [v]
    · iexists _; iexact v
    ipureintro; omega
  wp_for IH
  wp_if_destruct
  · icases v with ⟨%y, v⟩
    have Hlt : n < bs.length := by word
    obtain ⟨x, Hx⟩ : ∃ x, bs[n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
    have hz : sint.Z (W64 (n : Int)) = n := by word
    wp_apply wp_load_slice_index s (sint.Z (W64 (n : Int))) _ dq x (by word) $$ [Hs] as Hs
    · iframe; ipureintro; rw [hz]; simpa using Hx
    try wp_auto
    generalize hc0 : List.foldl (hash.crc32.crcUpdByte ta.arr) (~~~c) (List.take n bs) = c0
    have hi0 : sint.Z (W64 (uint.Z (W8 (uint.Z c0) ^^^ x))) = ((W8 (uint.Z c0) ^^^ x).toNat : Int) := by
      have := BitVec.isLt (W8 (uint.Z c0) ^^^ x)
      simp only [uint.Z, sint.Z]
      word
    obtain ⟨k, hk⟩ : ∃ k : Nat, k = (W8 (uint.Z c0) ^^^ x).toNat := ⟨_, rfl⟩
    have hk256 : k < 256 := by rw [hk]; exact BitVec.isLt _
    have hi : sint.Z (W64 (uint.Z (W8 (uint.Z c0) ^^^ x))) = k := by rw [hi0, hk]
    rw [hi, ite_eq_left_of_eq_true _ _ (eq_true (⟨by omega, by omega⟩ : (0 : Int) ≤ k ∧ (k : Int) < 256))]
    obtain ⟨e, he⟩ : ∃ e, ta.arr[(k : Int).toNat]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by simp; omega)⟩
    icases array_acc tab k _ 256 _ _ (by omega) he $$ Ht with ⟨He, Hback⟩
    wp_auto
    ihave Ht := Hback $$ He
    rw [list_set_getElem?_self _ _ _ he]
    wp_for_post
    iframe
    iexists (n + 1)
    have hstep : hash.crc32.crcUpdByte ta.arr c0 x = e ^^^ c0 >>> W64 8 := by
      have hw : W8 (uint.Z c0) = BitVec.ofNat 8 c0.toNat := by word
      have hs8 : c0 >>> W64 8 = c0 >>> 8 := rfl
      have he' : ta.arr.getD (BitVec.ofNat 8 c0.toNat ^^^ x).toNat 0#32 = e := by
        rw [List.getD_eq_getElem?_getD, ← hw, ← hk]; simp only [Int.toNat_natCast] at he; rw [he]; rfl
      simp only [hash.crc32.crcUpdByte, he', hs8]
    rw [show W64 (n : Int) + W64 1 = W64 ((n + 1 : Nat) : Int) by word,
      List.take_add_one, Hx, Option.toList_some, List.foldl_append, hc0, List.foldl_cons,
      List.foldl_nil, hstep]
    iframe
    isplitl [v]
    · iexists _; iexact v
    ipureintro; omega
  · have Hn' : n = bs.length := by word
    subst Hn'
    rw [List.take_length]
    unfold hash.crc32.crcUpdate
    iapply HΦ
    iframe

end proof

end EtcdGrove
end Perennial
