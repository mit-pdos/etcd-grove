/-
The proof of `modelReadLine` (`Net/Spec/net/http/modelReadLine.lean`): a loop of
`bufio.Reader.ReadByte` (`Spec/bufio/Reader__ReadByte.lean`) appending to `line`; the invariant: the
reader has delivered `l` after `r`, the bytes of `line`, with no `"\n"` among them.
-/
module

public import Net.Spec.net.http.modelReadLine
public import Spec.bufio.Reader__ReadByte

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace net.http

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

set_option goose.wp.extras true

theorem modelReadLine.last_idx (l : List w8) (sl : GoSlice) (hlen : l.length = sint.nat sl.len)
    (hpos : 0 < sint.Z sl.len) :
    (sint.Z (sl.len - W64 1)).toNat = l.length - 1 ∧ l.length - 1 < l.length := by
  have h1 : sint.Z (sl.len - W64 1) = sint.Z sl.len - 1 := by word
  have hlz : (l.length : Int) = sint.Z sl.len := by
    rw [hlen]; show ((sint.Z sl.len).toNat : Int) = _; omega
  rw [h1]; omega

theorem modelReadLine.wp_proof
    (wp_ReadByte : EtcdGrove.bufio.Reader.ReadByte.spec (GF := GF) (hG := hG)) :
    modelReadLine.spec (GF := GF) (hG := hG) := by
  intro b ri S E r
  iintro #Hrd #HSb
  wp_start as Hb
  wp_auto
  ihave HI : (∃ (sl : GoSlice) (l : List w8),
      "line" ∷ line_ptr ↦ sl ∗ "Hsl" ∷ sl ↦* l ∗ "Hcap" ∷ ownSliceCap w8 sl (DFrac.own 1) ∗
      "Hb" ∷ EtcdGrove.bufio.ownReader b ri S E (r ++ l) ∗ "%Hl" ∷ ⌜W8 10 ∉ l⌝ : IProp GF)
      $$ [line Hb]
  · iexists slice.nil, []
    rw [List.append_nil]
    iframe line Hb
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    ipureintro; simp
  wp_for HI
  ihave #HRB := wp_ReadByte b ri S E (r ++ l) $$ Hrd HSb
  wp_apply HRB $$ Hb as %c %err (⟨%Herr, Hb⟩ | ⟨%Herr, #HE, Hb⟩)
  · subst Herr
    wp_auto
    ihave %Hlen := ownSlice_len $$ Hsl
    wp_if_destruct
    · -- the end of the line
      wp_if_destruct
      · -- `line` not empty: its last byte
        have hpos : 0 < sint.Z sl.len := by revert Hif; word
        obtain ⟨hidx, hlt⟩ := modelReadLine.last_idx l sl Hlen.1 hpos
        obtain ⟨x, hx⟩ : ∃ x, l[(sint.Z (sl.len - W64 1)).toNat]? = some x :=
          ⟨_, List.getElem?_eq_getElem (by rw [hidx]; exact hlt)⟩
        have hlast : l.getLast? = some x := by
          rw [List.getLast?_eq_getElem?, ← hx, hidx]
        rw [ite_eq_left_of_eq_true _ _ (eq_true (show _ ∧ _ from ⟨by word, by word⟩))]
        wp_apply (wp_load_slice_index sl (sint.Z (sl.len - W64 1)) l (DFrac.own 1) x (by word)) $$ [Hsl] as Hsl
        · iframe; ipureintro; exact hx
        try wp_auto
        wp_if_destruct
        · -- a final `"\r"`: dropped
          ihave %Hwf := ownSlice_wf $$ Hsl
          rw [ite_eq_left_of_eq_true _ _ (eq_true (show _ ∧ _ ∧ _ from ⟨by word, by word, by word⟩))]
          try wp_auto
          icases (ownSlice_split_all (sl.len - W64 1) sl _ l ⟨by word, by word⟩).1 $$ Hsl with ⟨Hs1, -⟩
          wp_apply (wp_bytes_to_string _ (l.take (sint.nat (sl.len - W64 1))) (DFrac.own 1)) $$ Hs1 as -
          try wp_auto
          wp_for_post
          iapply HΦ
          iexists l
          isplitr
          · ipureintro; exact Hl
          ileft
          iframe Hb
          ipureintro
          refine ⟨rfl, ?_⟩
          unfold dropCR; rw [hlast]
          simp only [ite_true, List.dropLast_eq_take]
          congr 1
        · wp_apply (wp_bytes_to_string sl l (DFrac.own 1)) $$ Hsl as Hsl
          try wp_auto
          wp_for_post
          iapply HΦ
          iexists l
          isplitr
          · ipureintro; exact Hl
          ileft
          iframe Hb
          ipureintro
          refine ⟨rfl, ?_⟩
          unfold dropCR; rw [hlast, ite_eq_right_iff.mpr (fun h => absurd (by simpa using h) Hif)]
      · -- `line` empty
        have hnil : l = [] := List.eq_nil_of_length_eq_zero (by revert Hif; word)
        subst hnil
        try wp_auto
        wp_apply (wp_bytes_to_string sl [] (DFrac.own 1)) $$ Hsl as Hsl
        try wp_auto
        wp_for_post
        iapply HΦ
        iexists []
        isplitr
        · ipureintro; simp
        ileft
        iframe Hb
        ipureintro; exact ⟨rfl, rfl⟩
    · -- another byte: appended
      wp_apply wp_slice_literal (V := w8) [c]
      isplitr
      · ipureintro; rfl
      iintro %lit ⟨Hlit, -⟩
      wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hsl $Hcap $Hlit] as %sl' ⟨Hsl', Hcap', -⟩
      try wp_auto
      wp_for_post
      iframe
      iexists sl', l ++ [c]
      rw [List.append_assoc]
      iframe
      ipureintro
      simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨Hl, fun h => Hif h.symm⟩
  · obtain ⟨i, rfl⟩ : ∃ i, err = GoInterface.ok i := by
      cases err with
      | nil => exact absurd rfl Herr
      | ok i => exact ⟨i, rfl⟩
    wp_auto
    ihave %Hlen := ownSlice_len $$ Hsl
    wp_if_destruct
    · wp_apply (wp_bytes_to_string sl l (DFrac.own 1)) $$ Hsl as Hsl
      try wp_auto
      wp_for_post
      iapply HΦ
      iexists l
      isplitr
      · ipureintro; exact Hl
      iright
      iexists GoInterface.ok i
      iframe HE Hb
      ipureintro
      refine ⟨Herr, Or.inl ⟨?_, rfl, rfl⟩⟩
      intro hl; subst hl; simp at Hlen; revert Hif; word
    · try wp_auto
      wp_for_post
      iapply HΦ
      iexists l
      isplitr
      · ipureintro; exact Hl
      iright
      iexists GoInterface.ok i
      iframe HE Hb
      ipureintro
      refine ⟨Herr, Or.inr ⟨?_, rfl, rfl⟩⟩
      apply List.eq_nil_of_length_eq_zero; revert Hif; word

end proof

end net.http
end Perennial
