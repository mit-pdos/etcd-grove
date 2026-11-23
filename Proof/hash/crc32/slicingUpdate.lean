/-
The proof of `Spec/hash/crc32/slicingUpdate.lean`: eight bytes a round (`slicing8_step`), the rest by
`simpleUpdate` of table `0`.
-/
module

public import Spec.hash.crc32.slicingUpdate
public import Spec.hash.crc32.simpleUpdate
public import Spec.internal.byteorder.LEUint32
public import Proof.hash.crc32.Slicing
public import Proof.hash.crc32.TableLemmas

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

namespace hash.crc32

theorem crcUpdate_split (T : List w32) (c : w32) (bs : List w8) (n : Nat) :
    _root_.Perennial.hash.crc32.crcUpdate T c bs =
      _root_.Perennial.hash.crc32.crcUpdate T (_root_.Perennial.hash.crc32.crcUpdate T c (bs.take n)) (bs.drop n) := by
  simp only [_root_.Perennial.hash.crc32.crcUpdate, BitVec.not_not]
  rw [← List.foldl_append, List.take_append_drop]

theorem crcUpdate_nil (T : List w32) (c : w32) : _root_.Perennial.hash.crc32.crcUpdate T c [] = c := by
  simp [_root_.Perennial.hash.crc32.crcUpdate]

theorem crcUpdByte_eq_step (poly : w32) :
    _root_.Perennial.hash.crc32.crcUpdByte (_root_.Perennial.hash.crc32.crcTableOf poly) =
      _root_.Perennial.hash.crc32.crcStep poly := by
  funext c v
  rw [_root_.Perennial.hash.crc32.crcUpdByte_tableOf]; rfl

theorem byte_idx (b : w8) : sint.Z (W64 (uint.Z b)) = ((b.toNat : Nat) : Int) := by
  have := BitVec.isLt b
  simp only [uint.Z, sint.Z]; word

theorem shr24_lt (x : w32) : (x >>> 24).toNat < 256 := by
  rw [BitVec.toNat_ushiftRight]
  have := BitVec.isLt x
  rw [Nat.shiftRight_eq_div_pow]
  omega

theorem shr24_idx (x : w32) : sint.Z (W64 (uint.Z (x >>> W64 24))) = (((x >>> 24).toNat : Nat) : Int) := by
  have := shr24_lt x
  have e : x >>> W64 24 = x >>> 24 := rfl
  rw [e]
  simp only [uint.Z, sint.Z]; word

theorem and255_lt (c : w32) : (c &&& 0xff#32).toNat < 256 := by
  rw [BitVec.toNat_and]
  have := @Nat.and_le_right c.toNat (0xff#32).toNat
  have h255 : (0xff#32).toNat = 255 := rfl
  omega

theorem and255_idx (c : w32) :
    sint.Z (W64 (uint.Z (c &&& W32 255))) = (((c &&& 0xff#32).toNat : Nat) : Int) := by
  have := and255_lt c
  have e : W32 255 = 0xff#32 := rfl
  rw [e]
  simp only [uint.Z, sint.Z]; word

theorem row0_arr (poly : w32) :
    (array.mk 256 ((List.range 256).map (_root_.Perennial.hash.crc32.slicingEntry poly 0)) : GoArray w32 256).arr =
      _root_.Perennial.hash.crc32.crcTableOf poly := by
  show (List.range 256).map (_root_.Perennial.hash.crc32.slicingEntry poly 0) =
    (List.range 256).map (_root_.Perennial.hash.crc32.crcTableEntry poly)
  congr 1

end hash.crc32

theorem hash.crc32.slicingUpdate.wp_proof
    (hsimple : hash.crc32.simpleUpdate.spec (GF := GF) (hG := hG))
    (hle : byteorder.LEUint32.spec (GF := GF) (hG := hG)) :
    hash.crc32.slicingUpdate.spec (GF := GF) (hG := hG) := by
  intro poly c tab s bs dq
  rw [hash.crc32.slicingTableArr_tabOf]
  wp_start as ⟨#Ht, Hs⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  try wp_auto
  wp_if_destruct
  · try wp_auto
    ihave HI : iprop(∃ (k : Nat) (s' : GoSlice),
        "p" ∷ p_ptr ↦ s' ∗
        "crc" ∷ crc_ptr ↦ List.foldl (_root_.Perennial.hash.crc32.crcStep poly) (~~~c) (bs.take (8 * k)) ∗
        "Hs" ∷ s' ↦*{dq} bs.drop (8 * k) ∗
        "Hback" ∷ (s' ↦*{dq} bs.drop (8 * k) -∗ s ↦*{dq} bs) ∗
        "%Hk" ∷ ⌜8 * k ≤ bs.length⌝) $$ [p crc Hs]
    · iexists 0, s
      simp only [Nat.mul_zero, List.take_zero, List.foldl_nil, List.drop_zero]
      iframe
      isplitl []
      · iintro H; iexact H
      ipureintro; omega
    wp_for HI
    ihave %Hl' := ownSlice_len _ _ _ $$ Hs
    try wp_auto
    wp_if_destruct
    · -- a round: eight bytes
      obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, rest, hd⟩ : ∃ b0 b1 b2 b3 b4 b5 b6 b7 rest,
          bs.drop (8 * k) = b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest := by
        generalize bs.drop (8 * k) = l at Hl'
        match l with
        | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest => exact ⟨_, _, _, _, _, _, _, _, _, rfl⟩
        | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] | [_, _, _, _, _, _]
          | [_, _, _, _, _, _, _] => exfalso; simp at Hl'; word
      rw [hd]
      generalize hcur : List.foldl (_root_.Perennial.hash.crc32.crcStep poly) (~~~c) (List.take (8 * k) bs) = cur
      wp_apply hle $$ [Hs] as Hs
      · iexact Hs
      try wp_auto
      -- `tab[0][p[7]] ^ tab[1][p[6]] ^ tab[2][p[5]] ^ tab[3][p[4]]`
      rw [show sint.Z (W64 0) = ((0 : Nat) : Int) from rfl]
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
      wp_apply wp_load_slice_index s' (sint.Z (W64 7)) _ dq b7 (by word) $$ [Hs] as Hs
      · iframe; ipureintro; rfl
      try wp_auto
      rw [hash.crc32.byte_idx, ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by have := BitVec.isLt b7; omega⟩)]
      wp_apply hash.crc32.wp_load_tabOf tab DFrac.discard _ 0 b7.toNat (by omega) (BitVec.isLt b7) $$ [] as -
      · iexact Ht
      try wp_auto
      rw [show sint.Z (W64 1) = ((1 : Nat) : Int) from rfl]
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
      wp_apply wp_load_slice_index s' (sint.Z (W64 6)) _ dq b6 (by word) $$ [Hs] as Hs
      · iframe; ipureintro; rfl
      try wp_auto
      rw [hash.crc32.byte_idx, ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by have := BitVec.isLt b6; omega⟩)]
      wp_apply hash.crc32.wp_load_tabOf tab DFrac.discard _ 1 b6.toNat (by omega) (BitVec.isLt b6) $$ [] as -
      · iexact Ht
      try wp_auto
      rw [show sint.Z (W64 2) = ((2 : Nat) : Int) from rfl]
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
      wp_apply wp_load_slice_index s' (sint.Z (W64 5)) _ dq b5 (by word) $$ [Hs] as Hs
      · iframe; ipureintro; rfl
      try wp_auto
      rw [hash.crc32.byte_idx, ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by have := BitVec.isLt b5; omega⟩)]
      wp_apply hash.crc32.wp_load_tabOf tab DFrac.discard _ 2 b5.toNat (by omega) (BitVec.isLt b5) $$ [] as -
      · iexact Ht
      try wp_auto
      rw [show sint.Z (W64 3) = ((3 : Nat) : Int) from rfl]
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
      wp_apply wp_load_slice_index s' (sint.Z (W64 4)) _ dq b4 (by word) $$ [Hs] as Hs
      · iframe; ipureintro; rfl
      try wp_auto
      rw [hash.crc32.byte_idx, ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by have := BitVec.isLt b4; omega⟩)]
      wp_apply hash.crc32.wp_load_tabOf tab DFrac.discard _ 3 b4.toNat (by omega) (BitVec.isLt b4) $$ [] as -
      · iexact Ht
      try wp_auto
      generalize hX : cur ^^^ byteorder.le32 b0 b1 b2 b3 = X
      rw [show sint.Z (W64 4) = ((4 : Nat) : Int) from rfl, hash.crc32.shr24_idx,
        ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by have := hash.crc32.shr24_lt X; omega⟩)]
      wp_apply hash.crc32.wp_load_tabOf tab DFrac.discard _ 4 _ (by omega) (hash.crc32.shr24_lt X) $$ [] as -
      · iexact Ht
      try wp_auto
      rw [show sint.Z (W64 5) = ((5 : Nat) : Int) from rfl, hash.crc32.and255_idx (X >>> W64 16),
        ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by have := hash.crc32.and255_lt (X >>> W64 16); omega⟩)]
      wp_apply hash.crc32.wp_load_tabOf tab DFrac.discard _ 5 _ (by omega) (hash.crc32.and255_lt (X >>> W64 16)) $$ [] as -
      · iexact Ht
      try wp_auto
      rw [show sint.Z (W64 6) = ((6 : Nat) : Int) from rfl, hash.crc32.and255_idx (X >>> W64 8),
        ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by have := hash.crc32.and255_lt (X >>> W64 8); omega⟩)]
      wp_apply hash.crc32.wp_load_tabOf tab DFrac.discard _ 6 _ (by omega) (hash.crc32.and255_lt (X >>> W64 8)) $$ [] as -
      · iexact Ht
      try wp_auto
      rw [show sint.Z (W64 7) = ((7 : Nat) : Int) from rfl, hash.crc32.and255_idx X,
        ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by have := hash.crc32.and255_lt X; omega⟩)]
      wp_apply hash.crc32.wp_load_tabOf tab DFrac.discard _ 7 _ (by omega) (hash.crc32.and255_lt X) $$ [] as -
      · iexact Ht
      try wp_auto
      icases ownSlice_wf s' _ _ $$ Hs with %Hwf
      have hlen8 : sint.Z (W64 8) ≤ sint.Z s'.len := by have := Hif; word
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, hlen8, Hwf.2⟩)]
      icases (ownSlice_split_all (W64 8) s' dq _ ⟨by word, hlen8⟩).1 $$ Hs with ⟨H0, H1⟩
      have hs8 : sint.nat (W64 8) = 8 := rfl
      rw [hs8]
      simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero]
      try wp_auto
      wp_for_post
      iframe
      iexists (k + 1), (slice.slice s' w8 (W64 8) s'.len)
      have hstep : List.foldl (_root_.Perennial.hash.crc32.crcStep poly) (~~~c) (List.take (8 * (k + 1)) bs) =
          _root_.Perennial.hash.crc32.slicingEntry poly 0 (BitVec.toNat b7) ^^^
            _root_.Perennial.hash.crc32.slicingEntry poly 1 (BitVec.toNat b6) ^^^
            _root_.Perennial.hash.crc32.slicingEntry poly 2 (BitVec.toNat b5) ^^^
            _root_.Perennial.hash.crc32.slicingEntry poly 3 (BitVec.toNat b4) ^^^
            _root_.Perennial.hash.crc32.slicingEntry poly 4 (X >>> 24).toNat ^^^
            _root_.Perennial.hash.crc32.slicingEntry poly 5 (BitVec.toNat (X >>> W64 16 &&& 255#32)) ^^^
            _root_.Perennial.hash.crc32.slicingEntry poly 6 (BitVec.toNat (X >>> W64 8 &&& 255#32)) ^^^
            _root_.Perennial.hash.crc32.slicingEntry poly 7 (BitVec.toNat (X &&& 255#32)) := by
        rw [show 8 * (k + 1) = 8 * k + 8 by omega, List.take_add, List.foldl_append, hcur, hd]
        simp only [List.take_succ_cons, List.take_zero]
        rw [_root_.Perennial.hash.crc32.slicing8_step, ← hX]
        rfl
      have hdrop : List.drop (8 * (k + 1)) bs = rest := by
        rw [show 8 * (k + 1) = 8 * k + 8 by omega, ← List.drop_drop, hd]; rfl
      rw [hstep, hdrop]
      iframe
      isplitl [Hback H0]
      · iintro H1
        iapply Hback
        ihave Hc := ownSlice_combine (W64 8) s' dq [b0, b1, b2, b3, b4, b5, b6, b7] rest (W64 0) s'.len
          ⟨by simp; rfl, by word, by word, hlen8⟩ $$ H0 H1
        rw [← slice_slice_trivial, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
          List.cons_append, List.cons_append, List.cons_append, List.cons_append, List.nil_append]
        iexact Hc
      ipureintro
      have := Hl'.1; simp only [hd, List.length_cons] at this
      have h2 := List.length_drop (l := bs) (i := 8 * k)
      rw [hd] at h2; simp at h2; omega
    · -- at most eight bytes left: `simpleUpdate` of table 0, unless none
      try wp_auto
      have hfold : ~~~List.foldl (_root_.Perennial.hash.crc32.crcStep poly) (~~~c) (List.take (8 * k) bs) =
          _root_.Perennial.hash.crc32.crcUpdate (_root_.Perennial.hash.crc32.crcTableOf poly) c
            (List.take (8 * k) bs) := by
        rw [_root_.Perennial.hash.crc32.crcUpdate, hash.crc32.crcUpdByte_eq_step]
      rw [hfold]
      wp_if_destruct
      · have hnil : List.drop (8 * k) bs = [] := by
          apply List.eq_nil_of_length_eq_zero; rw [Hl'.1, Hif]; rfl
        try wp_auto
        ihave Hs := Hback $$ Hs
        rw [hash.crc32.crcUpdate_split _ c bs (8 * k), hnil, hash.crc32.crcUpdate_nil]
        iapply HΦ $$ Hs
      · rw [show sint.Z (W64 0) = ((0 : Nat) : Int) from rfl]
        ihave #Hr0 := hash.crc32.tabOf_row_persist tab (_root_.Perennial.hash.crc32.slicingEntry poly) 0 (by omega) $$ Ht
        wp_apply hsimple $$ [Hs] as ⟨-, Hs⟩
        · iframe Hs; iexact Hr0
        try wp_auto
        ihave Hs := Hback $$ Hs
        rw [hash.crc32.row0_arr, ← hash.crc32.crcUpdate_split]
        iapply HΦ $$ Hs
  · -- fewer than 16 bytes: `simpleUpdate` of table 0, unless `p` is empty
    try wp_auto
    wp_if_destruct
    · have hnil : bs = [] := by
        apply List.eq_nil_of_length_eq_zero; rw [Hlen.1, Hif]; rfl
      subst hnil
      try wp_auto
      rw [hash.crc32.crcUpdate_nil]
      iapply HΦ $$ Hs
    · have hz0 : sint.Z (W64 0) = ((0 : Nat) : Int) := rfl
      rw [hz0]
      ihave #Hr0 := hash.crc32.tabOf_row_persist tab (_root_.Perennial.hash.crc32.slicingEntry poly) 0 (by omega) $$ Ht
      wp_apply hsimple $$ [Hs] as ⟨-, Hs⟩
      · iframe Hs; iexact Hr0
      try wp_auto
      rw [hash.crc32.row0_arr]
      iapply HΦ $$ Hs

end proof

end EtcdGrove
end Perennial
