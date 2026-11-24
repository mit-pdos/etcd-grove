/-
The proof of `jsoncodec.AppendString` (`Net/Spec/models_lab/jsoncodec/AppendString.lean`).
-/
module

public import Net.Spec.models_lab.jsoncodec.AppendString
public import Net.Spec.models_lab.jsoncodec.appendEscapedASCII
public import Net.Spec.models_lab.jsoncodec.seqLen

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace models_lab.jsoncodec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : models_lab.jsoncodec.Assumptions]

set_option goose.wp.extras true

/-- `s[i:i+k]` in range, as `Slice go.string` reduces it. -/
theorem strSlice_some (s : List w8) (i : w64) (k : Nat) (h : uint.nat i + k ≤ s.length)
    (hlen : s.length < 2 ^ 63) :
    (if 0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z (i + W64 (k : Int)) ∧
        sint.Z (i + W64 (k : Int)) ≤ (s.length : Int) then
      Val #(List.take (sint.nat (i + W64 (k : Int)) - sint.nat i) (List.drop (sint.nat i) s))
     else Panic "slice bounds out of range") = Val #((s.drop (uint.nat i)).take k) := by
  have h1 : 0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z (i + W64 (k : Int)) ∧
      sint.Z (i + W64 (k : Int)) ≤ (s.length : Int) := by word
  have h2 : sint.nat (i + W64 (k : Int)) - sint.nat i = k := by word
  have h3 : sint.nat i = uint.nat i := by word
  rw [h2]
  simp only [h1, and_self, ↓reduceIte, h3]

theorem w64_small_iff (k m : Nat) (hk : k ≤ 4) (hm : m ≤ 4) :
    W64 (k : Int) = W64 (m : Int) ↔ k = m := by
  constructor
  · intro h; word
  · intro h; rw [h]

theorem AppendString.wp_proof (wp_esc : appendEscapedASCII.spec (GF := GF) (hG := hG))
    (wp_seqLen : seqLen.spec (GF := GF) (hG := hG)) :
    AppendString.spec (GF := GF) (hG := hG) := by
  intro b bs s
  wp_start as ⟨Hb, Hcap⟩
  wp_auto
  wp_apply wp_slice_literal (V := w8)
  isplitr
  · ipureintro; rfl
  iintro %lsl ⟨Hlsl, -⟩
  wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hlsl] as %b1 ⟨Hb, Hcap, -⟩
  try wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %hlen
  try wp_auto
  ihave HI : (∃ (i : w64) (o : GoSlice) (pre : List w8),
      "i" ∷ i_ptr ↦ i ∗ "out" ∷ out_ptr ↦ o ∗ "Hb" ∷ o ↦* (bs ++ [W8 34] ++ pre) ∗
      "Hcap" ∷ ownSliceCap w8 o (DFrac.own 1) ∗
      "%Hi" ∷ ⌜uint.nat i ≤ s.length ∧ pre ++ quoteFrom s (uint.nat i) = quoteFrom s 0⌝ :
      IProp GF) $$ [i out Hb Hcap]
  · iexists (W64 0), b1, []
    simp only [List.append_nil]
    iframe
    ipureintro
    exact ⟨by word, rfl⟩
  wp_for HI
  wp_if_destruct
  · have hlt : uint.nat i < s.length := by simp at Hif; word
    rw [strIdx_some s i hlt hlen]
    wp_auto
    wp_if_destruct
    · wp_apply wp_esc $$ [$Hb $Hcap] as %o' ⟨Hb, Hcap⟩
      try wp_auto
      wp_for_post
      have hc := lt128_of_uintZ _ Hif
      iframe
      iexists (i + W64 1), o', pre ++ escASCII (s.getD (uint.nat i) (W8 0))
      iframe
      isplitl [Hb]
      · iapply (slice_pts_eq _ _ _ ?_) $$ Hb
        simp only [List.append_assoc]
      · ipureintro
        have e1 : uint.nat (i + W64 1) = uint.nat i + 1 := by word
        refine ⟨by word, ?_⟩
        rw [e1, List.append_assoc, ← quoteFrom_ascii s _ hlt hc]
        exact Hi.2
    · wp_apply wp_seqLen s i hlt
      try wp_auto
      have hk := seqLenAt_le s (uint.nat i) hlt
      have hk1 := seqLenAt_pos s (uint.nat i)
      have hk4 : seqLenAt s (uint.nat i) ≤ 4 := seqLenB_le4 _ _ _ _
      have hc : ¬ (s.getD (uint.nat i) (W8 0)).toNat < 0x80 := by
        intro h; apply Hif; rw [uintZ_w8, uintZ_w8]; have : (W8 128 : w8).toNat = 128 := rfl; omega
      have k1 : W64 ((seqLenAt s (uint.nat i) : Nat) : Int) = W64 1 ↔ seqLenAt s (uint.nat i) = 1 :=
        w64_small_iff _ 1 hk4 (by omega)
      have k3 : W64 ((seqLenAt s (uint.nat i) : Nat) : Int) = W64 3 ↔ seqLenAt s (uint.nat i) = 3 :=
        w64_small_iff _ 3 hk4 (by omega)
      have e1 : uint.nat (i + W64 1) = uint.nat i + 1 := by word
      have e2 : uint.nat (i + W64 2) = uint.nat i + 2 := by word
      have ek : uint.nat (i + W64 ((seqLenAt s (uint.nat i) : Nat) : Int)) =
          uint.nat i + seqLenAt s (uint.nat i) := by word
      repeat' (first
        | wp_if_destruct
        | (rw [strIdx_some s _ (by word) hlen])
        | (rw [strSlice_some s i _ hk hlen])
        | wp_auto
        | (wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
           wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hsl] as %o' ⟨Hb, Hcap, -⟩))
      all_goals
        wp_for_post
        iframe
        iexists (i + W64 ((seqLenAt s (uint.nat i) : Nat) : Int)), o',
          pre ++ nonASCIIPiece s (uint.nat i) (seqLenAt s (uint.nat i))
        iframe
        isplitl [Hb]
        · iapply (slice_pts_eq _ _ _ ?_) $$ Hb
          simp only [List.append_assoc, List.append_cancel_left_eq]
          simp only [e1, e2, k1, k3] at *
          unfold nonASCIIPiece
          simp_all
        · ipureintro
          refine ⟨by word, ?_⟩
          rw [ek, List.append_assoc, ← quoteFrom_nonascii s _ hlt hc]
          exact Hi.2
  · have hge : s.length ≤ uint.nat i := by simp at Hif; word
    wp_apply wp_slice_literal (V := w8)
    isplitr
    · ipureintro; rfl
    iintro %lsl2 ⟨Hlsl, -⟩
    wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hlsl] as %b2 ⟨Hb, Hcap, -⟩
    try wp_auto
    iapply HΦ
    iframe Hcap
    iapply (slice_pts_eq _ _ _ ?_) $$ Hb
    have h2 := Hi.2
    rw [quoteFrom_end s _ hge, List.append_nil] at h2
    unfold jsonQuote
    rw [← h2]
    simp only [List.append_assoc]

end proof

end models_lab.jsoncodec
end Perennial
