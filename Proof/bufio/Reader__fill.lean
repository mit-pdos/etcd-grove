/-
`(*bufio.Reader).fill` (see `Spec/bufio/Reader__fill.lean`).
-/
module

public import Spec.bufio.Reader__fill

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.bufio.Assumptions]

theorem bufio.subslice_length' {α : Type} (a b : Nat) (l : List α) (h : b ≤ l.length) :
    (subslice a b l).length = b - a := by
  simp only [subslice, List.length_drop, List.length_take]; omega

theorem bufio.Reader.fill.wp_proof : bufio.Reader.fill.spec (GF := GF) (hG := hG) := by
  intro b ri S E r
  iintro #Hrd #HSb
  wp_start as Hb
  iunfold bufio.ownReaderBuf at Hb
  icases Hb with ⟨#Hpkg, %v, %bs, Hv, Hbuf, %Hwf, HS, #Herr⟩
  ihave %Hblen := ownSlice_len _ _ _ $$ Hbuf
  have hrw : v.r' = v.w' := by
    obtain ⟨_, h1, h2, h3, _, _, hq, _⟩ := Hwf
    have := congrArg List.length hq
    rw [bufio.subslice_length' _ _ bs h3] at this
    simp at this; revert h1 h2 this; word
  ihave %Hbwf := ownSlice_wf v.buf' _ bs $$ Hbuf
  try wp_auto
  wp_join iprop(b_ptr ↦ b ∗ b ↦ { v with r' := W64 0, w' := W64 0 }) with [Hv b] as ⟨b, Hv⟩
  · try wp_auto
    have hwlen : sint.Z v.w' ≤ sint.Z v.buf'.len := by
      have := Hwf.2.2.2.1; rw [Hblen.1] at this; word
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z v.r' ∧ sint.Z v.r' ≤ sint.Z v.w' ∧
        sint.Z v.w' ≤ sint.Z v.buf'.cap from ⟨Hwf.2.1, Hwf.2.2.1, by omega⟩))]
    try wp_auto
    wp_apply (wp_slice_copy_of_len_zero (V := w8) v.buf' (slice.slice v.buf' w8 v.r' v.w')
      (by simp [slice.slice, hrw]))
    try wp_auto
    have h00 : v.w' - v.w' = W64 0 := by word
    rw [hrw]
    simp only [h00]
    iframe
  · try wp_auto
    have h0 : v.r' = W64 0 := by revert Hif Hwf; word
    have hv : ({ v with r' := W64 0, w' := W64 0 } : _root_.Perennial.bufio.Reader) = v := by
      cases v; simp only at h0 hrw ⊢; rw [← hrw, h0]
    rw [hv]
    iframe
  wp_if_destruct
  · exfalso; have := Hwf.2.2.2.2.1; rw [Hblen.1] at this; revert Hif this; word
  try wp_auto
  wp_for
  rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z v.buf'.len ∧
      sint.Z v.buf'.len ≤ sint.Z v.buf'.cap from ⟨by decide, Hbwf.1, Hbwf.2⟩)),
    ← slice_slice_trivial (V := w8)]
  rw [Hwf.1]
  try wp_auto
  iunfold io.readerStreamNE at Hrd
  ihave %HSr := HSb $$ HS
  wp_apply Hrd $$ %r %v.buf' %bs [HS Hbuf] as %nr %er ⟨%ys, %Hys, #Hye, Hbuf, HS⟩
  · simp only [List.append_nil]; iframe; ipureintro; simp at HSr; have := Hwf.2.2.2.2.2.1; omega
  have hnr0 : ¬ sint.Z nr < 0 := by omega
  wp_if_destruct
  · exact absurd Hif hnr0
  have hys0 : ys.length ≤ bs.length := Hys.2.1
  have hBS : (ys ++ bs.drop ys.length).length = bs.length := by
    simp only [List.length_append, List.length_drop]; omega
  have hw : sint.nat (W64 0 + nr) = ys.length := by word
  have hsub : subslice (sint.nat (W64 0)) (sint.nat (W64 0 + nr)) (ys ++ bs.drop ys.length) = ys := by
    have h0 : sint.nat (W64 0) = 0 := by word
    rw [hw, h0]; simp [subslice]
  have hbne : bs ≠ [] := List.ne_nil_of_length_pos Hwf.2.2.2.2.1
  try wp_auto
  rcases her : er with e | _
  · simp only []
    try wp_auto
    wp_for_post
    iapply HΦ
    iexists ys, (GoInterface.ok e)
    isplitr
    · ipureintro; right; simp
    iunfold bufio.ownReaderBuf
    iframe Hpkg
    iexists _, (ys ++ bs.drop ys.length)
    iframe Hv Hbuf
    rw [← her]
    iframe HS Hye
    ipureintro
    refine ⟨rfl, by word, by word, ?_, ?_, ?_, ?_, rfl⟩
    · rw [hBS, hw]; exact hys0
    · rw [hBS]; exact Hwf.2.2.2.2.1
    · rw [hBS]; exact Hwf.2.2.2.2.2.1
    · exact hsub
  · simp only []
    try wp_auto
    have hyne : ys ≠ [] := by
      rcases Hys.2.2 hbne with h | h
      · exact h
      · exact absurd her h
    wp_if_destruct
    · wp_for_post
      iapply HΦ
      iexists ys, GoInterface.nil
      isplitr
      · ipureintro; left; exact hyne
      iunfold bufio.ownReaderBuf
      iframe Hpkg
      iexists _, (ys ++ bs.drop ys.length)
      iframe Hv Hbuf
      rw [← her]
      iframe HS Hye
      ipureintro
      refine ⟨rfl, by word, by word, ?_, ?_, ?_, ?_, (Hwf.2.2.2.2.2.2.2).trans her.symm⟩
      · rw [hBS, hw]; exact hys0
      · rw [hBS]; exact Hwf.2.2.2.2.1
      · rw [hBS]; exact Hwf.2.2.2.2.2.1
      · exact hsub
    · exfalso
      apply hyne
      apply List.eq_nil_of_length_eq_zero
      have h1 := Hys.1
      have h2 : sint.Z (W64 0) = 0 := by decide
      omega

end proof

end EtcdGrove
end Perennial
