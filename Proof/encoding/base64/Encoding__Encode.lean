/-
The proof of `Spec/encoding/base64/Encoding__Encode.lean`: the loop over the 3-byte groups writes
their 4 symbols each, `src` and `dst` advancing by 3 and 4 (as sub-slices of the arguments); then
the last group's 2 or 3 symbols and the padding. Lean-first.
-/
module

public import Spec.encoding.base64.Encoding__Encode
public import Proof.encoding.base64.Lemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.encoding.base64.Assumptions]

set_option maxHeartbeats 1600000 in
theorem base64.Encoding.Encode.wp_proof :
    base64.Encoding.Encode.spec (GF := GF) (hG := hG) := by
  intro e enc dqe dst src out d dq hlen
  wp_start as ⟨He, Hdst, Hsrc⟩
  icases base64.enc_open e enc dqe $$ He with ⟨%Hnn, Hf⟩
  icases Hf with ⟨Henc, Hdm, Hpad, Hstrict⟩
  try wp_auto
  ihave %Hsl := ownSlice_len _ _ _ $$ Hsrc
  ihave %Hdl := ownSlice_len _ _ _ $$ Hdst
  wp_if_destruct
  · -- nothing to encode
    have hd : d = [] := by
      apply List.eq_nil_of_length_eq_zero; rw [Hsl.1, Hif]; rfl
    subst hd
    have ho : out = [] := by
      apply List.eq_nil_of_length_eq_zero; rw [hlen]; simp [base64.encLen]
    subst ho
    try wp_auto
    iapply HΦ
    iframe
    iapply base64.enc_close e enc dqe Hnn
    unfold base64.encFields
    iframe
  · try wp_auto
    ihave %Hsw := ownSlice_wf _ _ _ $$ Hsrc
    ihave %Hdw := ownSlice_wf _ _ _ $$ Hdst
    ihave HI : (∃ (k : Nat), "src" ∷ src_ptr ↦ slice.slice src w8 (W64 ((3 * k : Nat) : Int)) src.len ∗
        "dst" ∷ dst_ptr ↦ slice.slice dst w8 (W64 ((4 * k : Nat) : Int)) dst.len ∗
        "Hsrc" ∷ src ↦*{dq} d ∗
        "Hdst" ∷ dst ↦* (_root_.Perennial.encoding.base64.b64Enc enc.encode'.arr
          (base64.padOf enc.padChar') (d.take (3 * k)) ++ out.drop (4 * k)) ∗
        "%Hk" ∷ ⌜3 * k ≤ d.length⌝ : IProp GF) $$ [src dst Hsrc Hdst]
    · iexists 0
      simp only [Nat.mul_zero, List.take_zero, List.drop_zero, _root_.Perennial.encoding.base64.b64Enc,
        List.nil_append]
      have h0 : W64 ((0 : Nat) : Int) = W64 0 := rfl
      rw [h0]
      isplitl [src]
      · rw [← slice_slice_trivial (V := w8) src]; iexact src
      isplitl [dst]
      · rw [← slice_slice_trivial (V := w8) dst]; iexact dst
      isplitl [Hsrc]
      · iexact Hsrc
      isplitl [Hdst]
      · iexact Hdst
      ipureintro; omega
    wp_for HI
    wp_if_destruct
    · have h3k : sint.Z (W64 ((3 * k : Nat) : Int)) = ((3 * k : Nat) : Int) := by word
      have hlt : 3 * k + 3 ≤ d.length := by
        have := Hsl.1; revert Hif; word
      have hs0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z (src.len - W64 ↑(3 * k)) := by word
      have hs1 : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) < sint.Z (src.len - W64 ↑(3 * k)) := by word
      have hs2 : 0 ≤ sint.Z (W64 2) ∧ sint.Z (W64 2) < sint.Z (src.len - W64 ↑(3 * k)) := by word
      have hi0 : (((3 * k : Nat) : Int) + sint.Z (W64 0)).toNat = 3 * k := by word
      have hi1 : (((3 * k : Nat) : Int) + sint.Z (W64 1)).toNat = 3 * k + 1 := by word
      have hi2 : (((3 * k : Nat) : Int) + sint.Z (W64 2)).toNat = 3 * k + 2 := by word
      have hp0 : 0 ≤ ((3 * k : Nat) : Int) + sint.Z (W64 0) := by word
      have hp1 : 0 ≤ ((3 * k : Nat) : Int) + sint.Z (W64 1) := by word
      have hp2 : 0 ≤ ((3 * k : Nat) : Int) + sint.Z (W64 2) := by word
      try wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true hs0), base64.sliceIndexRef_slice, h3k]
      wp_apply (wp_load_slice_index src _ d dq (d[3 * k]'(by omega)) hp0) $$ [Hsrc]
      · iframe; ipureintro; rw [hi0]; simp
      iintro Hsrc
      try wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true hs1), base64.sliceIndexRef_slice, h3k]
      wp_apply (wp_load_slice_index src _ d dq (d[3 * k + 1]'(by omega)) hp1) $$ [Hsrc]
      · iframe; ipureintro; rw [hi1]; simp
      iintro Hsrc
      try wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true hs2), base64.sliceIndexRef_slice, h3k]
      wp_apply (wp_load_slice_index src _ d dq (d[3 * k + 2]'(by omega)) hp2) $$ [Hsrc]
      · iframe; ipureintro; rw [hi2]; simp
      iintro Hsrc
      try wp_auto
      have hpre : (_root_.Perennial.encoding.base64.b64Enc enc.encode'.arr (base64.padOf enc.padChar')
          (d.take (3 * k))).length = 4 * k := by
        rw [base64.b64Enc_length, List.length_take, Nat.min_eq_left Hk]; unfold base64.encLen; split <;> omega
      have hout : 4 * k + 4 ≤ out.length := by rw [hlen]; unfold base64.encLen; split <;> omega
      have h4k : sint.Z (W64 ((4 * k : Nat) : Int)) = ((4 * k : Nat) : Int) := by
        have := Hdl.1; word
      have hd0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z (dst.len - W64 ↑(4 * k)) := by word
      have hd1 : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) < sint.Z (dst.len - W64 ↑(4 * k)) := by word
      have hd2 : 0 ≤ sint.Z (W64 2) ∧ sint.Z (W64 2) < sint.Z (dst.len - W64 ↑(4 * k)) := by word
      have hd3 : 0 ≤ sint.Z (W64 3) ∧ sint.Z (W64 3) < sint.Z (dst.len - W64 ↑(4 * k)) := by word
      have hj3 : (((4 * k : Nat) : Int) + sint.Z (W64 3)).toNat = 4 * k + 3 := by word
      have hq3 : 0 ≤ ((4 * k : Nat) : Int) + sint.Z (W64 3) := by word
      have hL : 4 * k + 3 < (_root_.Perennial.encoding.base64.b64Enc enc.encode'.arr
          (base64.padOf enc.padChar') (d.take (3 * k)) ++ out.drop (4 * k)).length := by
        rw [List.length_append, hpre, List.length_drop]; omega
      rw [ite_eq_left_of_eq_true _ _ (eq_true hd3), base64.sliceIndexRef_slice, h4k]
      wp_apply (wp_load_slice_index dst _ _ (DFrac.own 1) (_ : List w8)[4 * k + 3] hq3) $$ [Hdst]
      · iframe; ipureintro; rw [hj3]; simp
      iintro Hdst
      try wp_auto
      obtain ⟨hv0, hv1, hv2, hv3⟩ := base64.idx3 (d[3 * k]'(by omega)) (d[3 * k + 1]'(by omega))
        (d[3 * k + 2]'(by omega))
      have hb0 := base64.idx_bound _ (base64.lt64 _ (base64.pc0 (d[3 * k]'(by omega))))
      rw [hv0, ite_eq_left_of_eq_true _ _ (eq_true hb0)]
      wp_apply (base64.wp_load_alpha e enc.encode' dqe _ hb0) $$ Henc as Henc
      try wp_auto
      have hj0 : (((4 * k : Nat) : Int) + sint.Z (W64 0)).toNat = 4 * k := by word
      have hj1 : (((4 * k : Nat) : Int) + sint.Z (W64 1)).toNat = 4 * k + 1 := by word
      have hj2 : (((4 * k : Nat) : Int) + sint.Z (W64 2)).toNat = 4 * k + 2 := by word
      have hq0 : 0 ≤ ((4 * k : Nat) : Int) + sint.Z (W64 0) := by word
      have hq1 : 0 ≤ ((4 * k : Nat) : Int) + sint.Z (W64 1) := by word
      have hq2 : 0 ≤ ((4 * k : Nat) : Int) + sint.Z (W64 2) := by word
      simp only [base64.sint_setWidth, Int.toNat_natCast]
      rw [ite_eq_left_of_eq_true _ _ (eq_true hd0), base64.sliceIndexRef_slice, h4k]
      wp_apply (wp_store_slice_index dst _ _ _) $$ [Hdst]
      · iframe; ipureintro; refine ⟨hq0, ?_⟩; rw [List.length_append, hpre, List.length_drop]; word
      iintro Hdst
      rw [hj0]
      try wp_auto
      have hj3' := hj3
      have hq3' := hq3
      have hb1 := base64.idx_bound _ (base64.lt64 _ (base64.pc1 (d[3 * k]'(by omega)) (d[3 * k + 1]'(by omega))))
      rw [hv1, ite_eq_left_of_eq_true _ _ (eq_true hb1)]
      wp_apply (base64.wp_load_alpha e enc.encode' dqe _ hb1) $$ Henc as Henc
      try wp_auto
      simp only [base64.sint_setWidth, Int.toNat_natCast]
      rw [ite_eq_left_of_eq_true _ _ (eq_true hd1), base64.sliceIndexRef_slice, h4k]
      wp_apply (wp_store_slice_index dst _ _ _) $$ [Hdst]
      · iframe; ipureintro; refine ⟨hq1, ?_⟩; simp only [List.length_set]
        rw [List.length_append, hpre, List.length_drop]; word
      iintro Hdst
      rw [hj1]
      try wp_auto
      have hb2 := base64.idx_bound _ (base64.lt64 _ (base64.pc2 (d[3 * k + 1]'(by omega)) (d[3 * k + 2]'(by omega))))
      rw [hv2, ite_eq_left_of_eq_true _ _ (eq_true hb2)]
      wp_apply (base64.wp_load_alpha e enc.encode' dqe _ hb2) $$ Henc as Henc
      try wp_auto
      simp only [base64.sint_setWidth, Int.toNat_natCast]
      rw [ite_eq_left_of_eq_true _ _ (eq_true hd2), base64.sliceIndexRef_slice, h4k]
      wp_apply (wp_store_slice_index dst _ _ _) $$ [Hdst]
      · iframe; ipureintro; refine ⟨hq2, ?_⟩; simp only [List.length_set]
        rw [List.length_append, hpre, List.length_drop]; word
      iintro Hdst
      rw [hj2]
      try wp_auto
      have hb3 := base64.idx_bound _ (base64.lt64 _ (base64.pc3 (d[3 * k + 2]'(by omega))))
      rw [hv3, ite_eq_left_of_eq_true _ _ (eq_true hb3)]
      wp_apply (base64.wp_load_alpha e enc.encode' dqe _ hb3) $$ Henc as Henc
      try wp_auto
      simp only [base64.sint_setWidth, Int.toNat_natCast]
      rw [ite_eq_left_of_eq_true _ _ (eq_true hd3), base64.sliceIndexRef_slice, h4k]
      wp_apply (wp_store_slice_index dst _ _ _) $$ [Hdst]
      · iframe; ipureintro; refine ⟨hq3, ?_⟩; simp only [List.length_set]
        rw [List.length_append, hpre, List.length_drop]; word
      iintro Hdst
      rw [hj3]
      try wp_auto
      have hsc : 0 ≤ sint.Z (W64 3) ∧ sint.Z (W64 3) ≤ sint.Z (src.len - W64 ↑(3 * k)) ∧
          sint.Z (src.len - W64 ↑(3 * k)) ≤ sint.Z (src.cap - W64 ↑(3 * k)) := by
        have := Hsw; word
      have hss : slice.slice (slice.slice src w8 (W64 ↑(3 * k)) src.len) w8 (W64 3)
          (src.len - W64 ↑(3 * k)) = slice.slice src w8 (W64 ↑(3 * (k + 1))) src.len := by
        rw [slice_slice _ _ _ _ _ (by word)]
        congr 1
        · word
        · word
      rw [ite_eq_left_of_eq_true _ _ (eq_true hsc), hss]
      try wp_auto
      have hdc : 0 ≤ sint.Z (W64 4) ∧ sint.Z (W64 4) ≤ sint.Z (dst.len - W64 ↑(4 * k)) ∧
          sint.Z (dst.len - W64 ↑(4 * k)) ≤ sint.Z (dst.cap - W64 ↑(4 * k)) := by
        have := Hdw; have := Hdl.1; word
      have hds : slice.slice (slice.slice dst w8 (W64 ↑(4 * k)) dst.len) w8 (W64 4)
          (dst.len - W64 ↑(4 * k)) = slice.slice dst w8 (W64 ↑(4 * (k + 1))) dst.len := by
        have := Hdl.1
        rw [slice_slice _ _ _ _ _ (by word)]
        congr 1
        · word
        · word
      rw [ite_eq_left_of_eq_true _ _ (eq_true hdc), hds]
      try wp_auto
      wp_for_post
      have heq : _root_.Perennial.encoding.base64.b64Enc enc.encode'.arr (base64.padOf enc.padChar')
            (d.take (3 * (k + 1))) ++ out.drop (4 * (k + 1)) =
          ((((_root_.Perennial.encoding.base64.b64Enc enc.encode'.arr (base64.padOf enc.padChar')
            (d.take (3 * k)) ++ out.drop (4 * k)).set (4 * k)
              (enc.encode'.arr.getD ((d[3 * k]'(by omega)) >>> 2).toNat 0)).set (4 * k + 1)
              (enc.encode'.arr.getD (((d[3 * k]'(by omega)) &&& 3) <<< 4 |||
                (d[3 * k + 1]'(by omega)) >>> 4).toNat 0)).set (4 * k + 2)
              (enc.encode'.arr.getD (((d[3 * k + 1]'(by omega)) &&& 15) <<< 2 |||
                (d[3 * k + 2]'(by omega)) >>> 6).toNat 0)).set (4 * k + 3)
              (enc.encode'.arr.getD (BitVec.toNat ((d[3 * k + 2]'(by omega)) &&& 63)) 0) := by
        rw [base64.set4 _ _ (4 * k) hpre _ _ _ _ (by rw [List.length_drop]; omega), base64.take_group d k hlt,
          base64.b64Enc_append _ _ _ _ (by simp only [List.length_take]; omega), List.drop_drop]
        simp only [_root_.Perennial.encoding.base64.b64Enc, List.append_assoc, List.cons_append,
          List.nil_append]
        rw [show 4 * (k + 1) = 4 * k + 4 by omega]
      iframe
      iexists (k + 1)
      rw [heq]
      iframe
      ipureintro; omega
    · -- the last group: 0, 1 or 2 bytes
      have h3k : sint.Z (W64 ((3 * k : Nat) : Int)) = ((3 * k : Nat) : Int) := by word
      have hr : d.length < 3 * k + 3 := by
        have := Hsl.1; revert Hif; word
      have hpre : (_root_.Perennial.encoding.base64.b64Enc enc.encode'.arr (base64.padOf enc.padChar')
          (d.take (3 * k))).length = 4 * k := by
        rw [base64.b64Enc_length, List.length_take, Nat.min_eq_left Hk]; unfold base64.encLen; split <;> omega
      have hsplit : d = d.take (3 * k) ++ d.drop (3 * k) := (List.take_append_drop _ _).symm
      have henc : _root_.Perennial.encoding.base64.b64Enc enc.encode'.arr (base64.padOf enc.padChar') d =
          _root_.Perennial.encoding.base64.b64Enc enc.encode'.arr (base64.padOf enc.padChar') (d.take (3 * k)) ++
          _root_.Perennial.encoding.base64.b64Enc enc.encode'.arr (base64.padOf enc.padChar') (d.drop (3 * k)) := by
        conv => lhs; rw [hsplit]
        exact base64.b64Enc_append _ _ _ _ (by simp only [List.length_take]; omega)
      try wp_auto
      wp_if_destruct
      · -- nothing left
        have hd : d.length = 3 * k := by have := Hsl.1; revert Hif; word
        have hdrop : d.drop (3 * k) = [] := List.drop_eq_nil_of_le (by omega)
        have hodrop : out.drop (4 * k) = [] := List.drop_eq_nil_of_le (by rw [hlen, hd]; unfold base64.encLen; split <;> omega)
        try wp_auto
        iapply HΦ
        rw [henc, hdrop, hodrop]
        simp only [_root_.Perennial.encoding.base64.b64Enc, List.append_nil]
        iframe
        iapply base64.enc_close e enc dqe Hnn
        unfold base64.encFields
        iframe
      · have hne0 := Hif
        have hge : 3 * k + 1 ≤ d.length := by have := Hsl.1; revert Hif; word
        have h4k : sint.Z (W64 ((4 * k : Nat) : Int)) = ((4 * k : Nat) : Int) := by
          have := Hdl.1
          have : 4 * k + 2 ≤ out.length := by rw [hlen]; unfold base64.encLen; split <;> omega
          word
        have hs0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z (src.len - W64 ↑(3 * k)) := by word
        have hi0 : (((3 * k : Nat) : Int) + sint.Z (W64 0)).toNat = 3 * k := by word
        have hp0 : 0 ≤ ((3 * k : Nat) : Int) + sint.Z (W64 0) := by word
        have hj0 : (((4 * k : Nat) : Int) + sint.Z (W64 0)).toNat = 4 * k := by word
        have hj1 : (((4 * k : Nat) : Int) + sint.Z (W64 1)).toNat = 4 * k + 1 := by word
        have hj2 : (((4 * k : Nat) : Int) + sint.Z (W64 2)).toNat = 4 * k + 2 := by word
        have hj3 : (((4 * k : Nat) : Int) + sint.Z (W64 3)).toNat = 4 * k + 3 := by word
        have hq0 : 0 ≤ ((4 * k : Nat) : Int) + sint.Z (W64 0) := by word
        have hq1 : 0 ≤ ((4 * k : Nat) : Int) + sint.Z (W64 1) := by word
        have hq2 : 0 ≤ ((4 * k : Nat) : Int) + sint.Z (W64 2) := by word
        have hq3 : 0 ≤ ((4 * k : Nat) : Int) + sint.Z (W64 3) := by word
        have hdlen : sint.Z (dst.len - W64 ↑(4 * k)) = (out.length : Int) - 4 * k := by
          have := Hdl.1
          have : 4 * k + 2 ≤ out.length := by rw [hlen]; unfold base64.encLen; split <;> omega
          word
        try wp_auto
        wp_if_destruct
        · -- one byte left
          have hd : d.length = 3 * k + 1 := by have := Hsl.1; revert Hif; word
          have hdrop : d.drop (3 * k) = [d[3 * k]'(by omega)] := by
            apply List.ext_getElem
            · simp only [List.length_drop, List.length_cons, List.length_nil]; omega
            · intro i h1 h2
              simp only [List.length_cons, List.length_nil] at h2
              rw [List.getElem_drop]; simp only [List.getElem_singleton]; congr 1; omega
          rw [ite_eq_left_of_eq_true _ _ (eq_true hs0), base64.sliceIndexRef_slice, h3k]
          wp_apply (wp_load_slice_index src _ d dq (d[3 * k]'(by omega)) hp0) $$ [Hsrc]
          · iframe; ipureintro; rw [hi0]; simp
          iintro Hsrc
          try wp_auto
          obtain ⟨hv0, hv1⟩ := base64.idx1 (d[3 * k]'(by omega))
          have hb0 := base64.idx_bound _ (base64.lt64 _ (base64.pc0 (d[3 * k]'(by omega))))
          rw [hv0, ite_eq_left_of_eq_true _ _ (eq_true hb0)]
          wp_apply (base64.wp_load_alpha e enc.encode' dqe _ hb0) $$ Henc as Henc
          try wp_auto
          simp only [base64.sint_setWidth, Int.toNat_natCast]
          have hd0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z (dst.len - W64 ↑(4 * k)) := by
            rw [hdlen]
            have : 4 * k + 2 ≤ out.length := by rw [hlen]; unfold base64.encLen; split <;> omega
            word
          rw [ite_eq_left_of_eq_true _ _ (eq_true hd0), base64.sliceIndexRef_slice, h4k]
          wp_apply (wp_store_slice_index dst _ _ _) $$ [Hdst]
          · iframe; ipureintro; refine ⟨hq0, ?_⟩; rw [List.length_append, hpre, List.length_drop]
            have : 4 * k + 2 ≤ out.length := by rw [hlen]; unfold base64.encLen; split <;> omega
            word
          iintro Hdst
          rw [hj0]
          try wp_auto
          have hb1 := base64.idx_bound _ (base64.lt64 _ (base64.pc1' (d[3 * k]'(by omega))))
          rw [hv1, ite_eq_left_of_eq_true _ _ (eq_true hb1)]
          wp_apply (base64.wp_load_alpha e enc.encode' dqe _ hb1) $$ Henc as Henc
          try wp_auto
          simp only [base64.sint_setWidth, Int.toNat_natCast]
          have hd1 : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) < sint.Z (dst.len - W64 ↑(4 * k)) := by
            rw [hdlen]
            have : 4 * k + 2 ≤ out.length := by rw [hlen]; unfold base64.encLen; split <;> omega
            word
          rw [ite_eq_left_of_eq_true _ _ (eq_true hd1), base64.sliceIndexRef_slice, h4k]
          wp_apply (wp_store_slice_index dst _ _ _) $$ [Hdst]
          · iframe; ipureintro; refine ⟨hq1, ?_⟩; simp only [List.length_set]
            rw [List.length_append, hpre, List.length_drop]
            have : 4 * k + 2 ≤ out.length := by rw [hlen]; unfold base64.encLen; split <;> omega
            word
          iintro Hdst
          rw [hj1]
          try wp_auto
          wp_if_destruct
          · -- no padding
            have hol : out.length = 4 * k + 2 := by
              rw [hlen, hd]; simp [base64.encLen, base64.padOf, Hif]; omega
            try wp_auto
            iapply HΦ
            rw [henc, hdrop, base64.set2 _ _ (4 * k) hpre _ _ (by rw [List.length_drop]; omega)]
            simp only [base64.padOf, Hif, ite_true, _root_.Perennial.encoding.base64.b64Enc, Option.toList,
              List.append_nil]
            iframe
            iapply base64.enc_close e enc dqe Hnn
            unfold base64.encFields
            rw [Hif]
            iframe
          · -- padding
            have hol : out.length = 4 * k + 4 := by
              rw [hlen, hd]; simp [base64.encLen, base64.padOf, Hif]; omega
            try wp_auto
            have hd2 : 0 ≤ sint.Z (W64 2) ∧ sint.Z (W64 2) < sint.Z (dst.len - W64 ↑(4 * k)) := by
              rw [hdlen]; word
            rw [ite_eq_left_of_eq_true _ _ (eq_true hd2), base64.sliceIndexRef_slice, h4k]
            wp_apply (wp_store_slice_index dst _ _ _) $$ [Hdst]
            · iframe; ipureintro; refine ⟨hq2, ?_⟩; simp only [List.length_set]
              rw [List.length_append, hpre, List.length_drop]; word
            iintro Hdst
            rw [hj2]
            try wp_auto
            have hd3 : 0 ≤ sint.Z (W64 3) ∧ sint.Z (W64 3) < sint.Z (dst.len - W64 ↑(4 * k)) := by
              rw [hdlen]; word
            rw [ite_eq_left_of_eq_true _ _ (eq_true hd3), base64.sliceIndexRef_slice, h4k]
            wp_apply (wp_store_slice_index dst _ _ _) $$ [Hdst]
            · iframe; ipureintro; refine ⟨hq3, ?_⟩; simp only [List.length_set]
              rw [List.length_append, hpre, List.length_drop]; word
            iintro Hdst
            rw [hj3]
            try wp_auto
            iapply HΦ
            rw [henc, hdrop, base64.set4 _ _ (4 * k) hpre _ _ _ _ (by rw [List.length_drop]; omega)]
            simp only [base64.padOf, Hif, ite_false, _root_.Perennial.encoding.base64.b64Enc, Option.toList,
              List.drop_drop]
            rw [List.drop_eq_nil_of_le (by omega : out.length ≤ 4 * k + 4)]
            simp only [List.append_nil, List.append_assoc, List.cons_append, List.nil_append]
            iframe
            iapply base64.enc_close e enc dqe Hnn
            unfold base64.encFields
            iframe
        · have hne1 := Hif
          wp_if_destruct
          · -- two bytes left
            have hd : d.length = 3 * k + 2 := by have := Hsl.1; revert hne0 hne1 Hif; word
            have hdrop : d.drop (3 * k) = [d[3 * k]'(by omega), d[3 * k + 1]'(by omega)] := by
              apply List.ext_getElem
              · simp only [List.length_drop, List.length_cons, List.length_nil]; omega
              · intro i h1 h2
                simp only [List.length_cons, List.length_nil] at h2
                rw [List.getElem_drop]
                rcases (by omega : i = 0 ∨ i = 1) with h' | h' <;> subst h' <;> simp
            have hs1 : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) < sint.Z (src.len - W64 ↑(3 * k)) := by
              have := Hsl.1; word
            have hi1 : (((3 * k : Nat) : Int) + sint.Z (W64 1)).toNat = 3 * k + 1 := by word
            have hp1 : 0 ≤ ((3 * k : Nat) : Int) + sint.Z (W64 1) := by word
            rw [ite_eq_left_of_eq_true _ _ (eq_true hs0), base64.sliceIndexRef_slice, h3k]
            wp_apply (wp_load_slice_index src _ d dq (d[3 * k]'(by omega)) hp0) $$ [Hsrc]
            · iframe; ipureintro; rw [hi0]; simp
            iintro Hsrc
            try wp_auto
            rw [ite_eq_left_of_eq_true _ _ (eq_true hs1), base64.sliceIndexRef_slice, h3k]
            wp_apply (wp_load_slice_index src _ d dq (d[3 * k + 1]'(by omega)) hp1) $$ [Hsrc]
            · iframe; ipureintro; rw [hi1]; simp
            iintro Hsrc
            try wp_auto
            obtain ⟨hv0, hv1, hv2⟩ := base64.idx2 (d[3 * k]'(by omega)) (d[3 * k + 1]'(by omega))
            have hb0 := base64.idx_bound _ (base64.lt64 _ (base64.pc0 (d[3 * k]'(by omega))))
            rw [hv0, ite_eq_left_of_eq_true _ _ (eq_true hb0)]
            wp_apply (base64.wp_load_alpha e enc.encode' dqe _ hb0) $$ Henc as Henc
            try wp_auto
            simp only [base64.sint_setWidth, Int.toNat_natCast]
            have hd0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z (dst.len - W64 ↑(4 * k)) := by
              rw [hdlen]
              have : 4 * k + 3 ≤ out.length := by rw [hlen]; unfold base64.encLen; split <;> omega
              word
            rw [ite_eq_left_of_eq_true _ _ (eq_true hd0), base64.sliceIndexRef_slice, h4k]
            wp_apply (wp_store_slice_index dst _ _ _) $$ [Hdst]
            · iframe; ipureintro; refine ⟨hq0, ?_⟩; rw [List.length_append, hpre, List.length_drop]
              have : 4 * k + 3 ≤ out.length := by rw [hlen]; unfold base64.encLen; split <;> omega
              word
            iintro Hdst
            rw [hj0]
            try wp_auto
            have hb1 := base64.idx_bound _ (base64.lt64 _ (base64.pc1 (d[3 * k]'(by omega)) (d[3 * k + 1]'(by omega))))
            rw [hv1, ite_eq_left_of_eq_true _ _ (eq_true hb1)]
            wp_apply (base64.wp_load_alpha e enc.encode' dqe _ hb1) $$ Henc as Henc
            try wp_auto
            simp only [base64.sint_setWidth, Int.toNat_natCast]
            have hd1 : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) < sint.Z (dst.len - W64 ↑(4 * k)) := by
              rw [hdlen]
              have : 4 * k + 3 ≤ out.length := by rw [hlen]; unfold base64.encLen; split <;> omega
              word
            rw [ite_eq_left_of_eq_true _ _ (eq_true hd1), base64.sliceIndexRef_slice, h4k]
            wp_apply (wp_store_slice_index dst _ _ _) $$ [Hdst]
            · iframe; ipureintro; refine ⟨hq1, ?_⟩; simp only [List.length_set]
              rw [List.length_append, hpre, List.length_drop]
              have : 4 * k + 3 ≤ out.length := by rw [hlen]; unfold base64.encLen; split <;> omega
              word
            iintro Hdst
            rw [hj1]
            try wp_auto
            have hb2 := base64.idx_bound _ (base64.lt64 _ (base64.pc2' (d[3 * k + 1]'(by omega))))
            rw [hv2, ite_eq_left_of_eq_true _ _ (eq_true hb2)]
            wp_apply (base64.wp_load_alpha e enc.encode' dqe _ hb2) $$ Henc as Henc
            try wp_auto
            simp only [base64.sint_setWidth, Int.toNat_natCast]
            have hd2 : 0 ≤ sint.Z (W64 2) ∧ sint.Z (W64 2) < sint.Z (dst.len - W64 ↑(4 * k)) := by
              rw [hdlen]
              have : 4 * k + 3 ≤ out.length := by rw [hlen]; unfold base64.encLen; split <;> omega
              word
            rw [ite_eq_left_of_eq_true _ _ (eq_true hd2), base64.sliceIndexRef_slice, h4k]
            wp_apply (wp_store_slice_index dst _ _ _) $$ [Hdst]
            · iframe; ipureintro; refine ⟨hq2, ?_⟩; simp only [List.length_set]
              rw [List.length_append, hpre, List.length_drop]
              have : 4 * k + 3 ≤ out.length := by rw [hlen]; unfold base64.encLen; split <;> omega
              word
            iintro Hdst
            rw [hj2]
            try wp_auto
            wp_if_destruct
            · -- no padding
              have hol : out.length = 4 * k + 3 := by
                rw [hlen, hd]; simp [base64.encLen, base64.padOf, Hif]; omega
              try wp_auto
              iapply HΦ
              rw [henc, hdrop, base64.set3 _ _ (4 * k) hpre _ _ _ (by rw [List.length_drop]; omega)]
              simp only [base64.padOf, Hif, ite_true, _root_.Perennial.encoding.base64.b64Enc, Option.toList,
                List.append_nil]
              iframe
              iapply base64.enc_close e enc dqe Hnn
              unfold base64.encFields
              rw [Hif]
              iframe
            · -- padding
              have hol : out.length = 4 * k + 4 := by
                rw [hlen, hd]; simp [base64.encLen, base64.padOf, Hif]; omega
              try wp_auto
              have hd3 : 0 ≤ sint.Z (W64 3) ∧ sint.Z (W64 3) < sint.Z (dst.len - W64 ↑(4 * k)) := by
                rw [hdlen]; word
              rw [ite_eq_left_of_eq_true _ _ (eq_true hd3), base64.sliceIndexRef_slice, h4k]
              wp_apply (wp_store_slice_index dst _ _ _) $$ [Hdst]
              · iframe; ipureintro; refine ⟨hq3, ?_⟩; simp only [List.length_set]
                rw [List.length_append, hpre, List.length_drop]; word
              iintro Hdst
              rw [hj3]
              try wp_auto
              iapply HΦ
              rw [henc, hdrop, base64.set4 _ _ (4 * k) hpre _ _ _ _ (by rw [List.length_drop]; omega)]
              simp only [base64.padOf, Hif, ite_false, _root_.Perennial.encoding.base64.b64Enc, Option.toList,
                List.drop_drop]
              rw [List.drop_eq_nil_of_le (by omega : out.length ≤ 4 * k + 4)]
              simp only [List.append_nil, List.append_assoc, List.cons_append, List.nil_append]
              iframe
              iapply base64.enc_close e enc dqe Hnn
              unfold base64.encFields
              iframe
          · exfalso
            have := Hsl.1
            revert hne0 hne1 Hif; word

end proof

end EtcdGrove
end Perennial
