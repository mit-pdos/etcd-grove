/-
The proof of `Spec/hash/crc32/simplePopulateTable.lean`: the two loops, entry by entry.
-/
module

public import Spec.hash.crc32.simplePopulateTable

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace hash.crc32

/-- The table after `i` rounds of the outer loop: the first `i` entries of `poly`'s table, the rest
as they were. -/
def popAfter (poly : w32) (a : List w32) (i : Nat) : List w32 :=
  (_root_.Perennial.hash.crc32.crcTableOf poly).take i ++ a.drop i

theorem crcBits_succ' (poly c : w32) (k : Nat) :
    _root_.Perennial.hash.crc32.crcBits poly (k + 1) c =
      _root_.Perennial.hash.crc32.crcBit poly (_root_.Perennial.hash.crc32.crcBits poly k c) := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    show _root_.Perennial.hash.crc32.crcBits poly (k + 1) (_root_.Perennial.hash.crc32.crcBit poly c) = _
    rw [ih]; rfl

theorem crcTableOf_length (poly : w32) : (_root_.Perennial.hash.crc32.crcTableOf poly).length = 256 := by
  simp [_root_.Perennial.hash.crc32.crcTableOf]

theorem crcBit_odd (poly c : w32) (h : c &&& W32 1 = W32 1) :
    _root_.Perennial.hash.crc32.crcBit poly c = c >>> W64 1 ^^^ poly := by
  have h1 : c &&& 1#32 = 1#32 := h
  simp only [_root_.Perennial.hash.crc32.crcBit, h1, ite_true]
  rfl

theorem crcBit_even (poly c : w32) (h : ¬ c &&& W32 1 = W32 1) :
    _root_.Perennial.hash.crc32.crcBit poly c = c >>> W64 1 := by
  have h1 : ¬ c &&& 1#32 = 1#32 := h
  simp only [_root_.Perennial.hash.crc32.crcBit, h1, ite_false]
  rfl

theorem popAfter_succ (poly : w32) (arr : List w32) (i : Nat) (hl : arr.length = 256) (hi : i < 256) :
    (popAfter poly arr i).set i (_root_.Perennial.hash.crc32.crcTableEntry poly i) =
      popAfter poly arr (i + 1) := by
  apply List.ext_getElem
  · simp [popAfter, crcTableOf_length, hl]; omega
  · intro k h1 h2
    simp only [popAfter, List.getElem_set] at *
    have hT := crcTableOf_length poly
    by_cases hk : i = k
    · subst hk
      simp only [ite_true]
      rw [List.getElem_append_left (by simp [hT]; omega)]
      simp [_root_.Perennial.hash.crc32.crcTableOf]
    · simp only [hk, ite_false]
      by_cases hlt : k < i
      · rw [List.getElem_append_left (by simp [hT]; omega), List.getElem_append_left (by simp [hT]; omega)]
        simp
      · rw [List.getElem_append_right (by simp [hT]; omega), List.getElem_append_right (by simp [hT]; omega)]
        simp [hT]
        congr 1
        omega

theorem popAfter_256 (poly : w32) (arr : List w32) (hl : arr.length = 256) :
    popAfter poly arr 256 = _root_.Perennial.hash.crc32.crcTableOf poly := by
  simp [popAfter, hl, List.take_of_length_le, crcTableOf_length]

end hash.crc32

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [hash.crc32.Assumptions]

/-- A store of the `i`-th entry of a `uint32` array (`base64.wp_store_arr`'s, at `uint32`). -/
theorem hash.crc32.wp_store_arr32 (l : Loc) (n : Int) (a : GoArray w32 n) (i : Int) (v : w32)
    (hi : 0 ≤ i ∧ i < n) :
    {{ (l ↦ a : IProp GF) }}
      (App (Val (GoInstruction (GoStore go.uint32))) (Val (PairV #(arrayIndexRef w32 i l) #v)))
    {{ RET #(); l ↦ (array.mk n (a.arr.set i.toNat v) : GoArray w32 n) }} := by
  iintro %Φ Ha HΦ
  obtain ⟨arr⟩ := a
  icases array_len _ _ _ _ $$ Ha with %Hlen
  have hlk : arr[i.toNat]? = some (arr.getD i.toNat 0) := by
    rw [List.getElem?_eq_getElem (by omega)]
    simp [List.getD, List.getElem?_eq_getElem (show i.toNat < arr.length by omega)]
  icases array_acc _ i (DFrac.own 1) n ⟨arr⟩ (arr.getD i.toNat 0) hi.1 hlk $$ Ha with ⟨Hv, Ha⟩
  wp_apply IntoValTyped.wp_store (t := go.uint32) _ _ _ $$ Hv as Hv
  iapply HΦ
  iapply Ha $$ Hv

theorem hash.crc32.simplePopulateTable.wp_proof :
    hash.crc32.simplePopulateTable.spec (GF := GF) (hG := hG) := by
  intro poly t a
  obtain ⟨arr⟩ := a
  wp_start as Ht
  icases array_len _ _ _ _ $$ Ht with %Hlen
  wp_auto
  ihave HI : (∃ (i : Nat), "i" ∷ i_ptr ↦ W64 (i : Int) ∗
      "Ht" ∷ t ↦ (array.mk 256 (hash.crc32.popAfter poly arr i) : GoArray w32 256) ∗
      "%Hi" ∷ ⌜i ≤ 256⌝ : IProp GF) $$ [i Ht]
  · iexists 0
    simp only [hash.crc32.popAfter, List.take_zero, List.drop_zero, List.nil_append]
    iframe
    ipureintro; omega
  wp_for HI
  wp_if_destruct
  · have hi256 : i < 256 := by
      revert Hif; word
    ihave HJ : (∃ (j : Nat), "j" ∷ j_ptr ↦ W64 (j : Int) ∗
        "crc" ∷ crc_ptr ↦ _root_.Perennial.hash.crc32.crcBits poly j (W32 (sint.Z (W64 (i : Int)))) ∗
        "%Hj" ∷ ⌜j ≤ 8⌝ : IProp GF) $$ [j crc]
    · iexists 0
      iframe
      ipureintro; omega
    wp_for HJ
    wp_if_destruct
    · have hj8 : j < 8 := by revert Hif; word
      wp_if_destruct
      · wp_for_post
        iframe
        iexists (j + 1)
        rw [show W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) by word,
          hash.crc32.crcBits_succ', hash.crc32.crcBit_odd _ _ Hif]
        iframe
        ipureintro; omega
      · wp_for_post
        iframe
        iexists (j + 1)
        rw [show W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) by word,
          hash.crc32.crcBits_succ', hash.crc32.crcBit_even _ _ Hif]
        iframe
        ipureintro; omega
    · have hj8 : j = 8 := by revert Hif; word
      subst hj8
      have hb : 0 ≤ sint.Z (W64 (i : Int)) ∧ sint.Z (W64 (i : Int)) < 256 := by word
      rw [ite_eq_left_of_eq_true _ _ (eq_true hb)]
      have hw : W32 (sint.Z (W64 (i : Int))) = BitVec.ofNat 32 i := by word
      have hti : (sint.Z (W64 (i : Int))).toNat = i := by word
      rw [hw]
      wp_apply (hash.crc32.wp_store_arr32 _ 256 _ _ _ hb) $$ Ht as Ht
      rw [hti, show _root_.Perennial.hash.crc32.crcBits poly 8 (BitVec.ofNat 32 i) =
        _root_.Perennial.hash.crc32.crcTableEntry poly i from rfl,
        hash.crc32.popAfter_succ _ _ _ (by omega) hi256]
      wp_for_post
      iframe
      iexists (i + 1)
      rw [show W64 (i : Int) + W64 1 = W64 ((i + 1 : Nat) : Int) by word]
      iframe
      ipureintro; omega
  · have hi : i = 256 := by revert Hif; word
    subst hi
    iapply HΦ
    rw [hash.crc32.popAfter_256 _ _ (by omega)]
    iexact Ht

end proof

end EtcdGrove
end Perennial
