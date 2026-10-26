/-
**An overlapping `append`**: `append(s[:a+1], s[a:]...)`, which shifts the elements from `a` on
one place right (`traceutil.Trace.InsertStep`'s insertion; unit P4, 2026-10-14). Perennial's
`wp_slice_append` takes the appended slice separately owned; here both arguments are parts of the
same slice. Go's `append` either grows `s[:a+1]` in place, which copies `s[a:]` onto
`s[a+1:len(s)+1]` (a memmove within one array: `wp_slice_copy_within`), or copies both into a new
array, one after the other (each read from the owned `s`). Derived from Perennial's slice library
(the body of `append`, as `wp_slice_append_dfrac`); no change to Perennial.
-/
module

public import Perennial.Golang.Theory.Slice

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-- The list `wp_slice_copy_within` gives for the in-place shift: `vs` grown by one slot `vs'`,
`vs[i:n]` copied onto `[i+1:n+1]`. -/
theorem list_shift_within {A : Type} (vs vs' : List A) (i n : Nat) (hn : vs.length = n)
    (h1 : vs'.length = 1) (hi : i < n) :
    (vs ++ vs').take (i + 1) ++
      ((subslice i n (vs ++ vs')).take (n + 1 - (i + 1)) ++
        (subslice (i + 1) (n + 1) (vs ++ vs')).drop (n - i)) ++
      (vs ++ vs').drop (n + 1) = vs.take (i + 1) ++ vs.drop i := by
  subst hn
  have ht : (vs ++ vs').take (i + 1) = vs.take (i + 1) := by
    rw [List.take_append_of_le_length (by omega)]
  have hs1 : subslice i vs.length (vs ++ vs') = vs.drop i := by
    simp [subslice]
  have hs2 : ((subslice (i + 1) (vs.length + 1) (vs ++ vs')).drop (vs.length - i)) = [] := by
    simp only [subslice, List.drop_drop]
    apply List.drop_of_length_le
    simp only [List.length_take, List.length_append, h1]; omega
  have hd : (vs ++ vs').drop (vs.length + 1) = [] := by
    apply List.drop_of_length_le; rw [List.length_append, h1]; exact Nat.le_refl _
  rw [ht, hs1, hs2, hd, List.append_nil, List.append_nil,
    List.take_of_length_le (l := List.drop i vs) (i := vs.length + 1 - (i + 1))
      (by rw [List.length_drop]; omega)]

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [preSem : go.PreSemantics]
variable {s : Stuckness} {E : CoPset}
variable {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]

/-- `append(s[:a+1], s[a:]...)` of an owned slice `s` (with its capacity), `0 ≤ a < len(s)`: a
slice of `s`'s elements up to `a` included, then those from `a` on (the element at `a` twice),
owned with its capacity. -/
theorem wp_slice_append_shift {st t : go.GoType} [st ↓u go.SliceType t]
    [IntoValTyped (GF := GF) V t] (sl : GoSlice) (vs : List V) (a : w64)
    (ha : 0 ≤ sint.Z a ∧ sint.Z a < sint.Z sl.len) :
    {{ (sl ↦* vs ∗ ownSliceCap V sl (DFrac.own 1) : IProp GF) }}
      (App (App (Val #(functions go.append [st])) (Val #(slice.slice sl V (W64 0) (a + W64 1))))
        (Val #(slice.slice sl V a sl.len))) @ s; E
    {{ (s' : GoSlice), RET #s';
        s' ↦* (vs.take (sint.nat a + 1) ++ vs.drop (sint.nat a)) ∗
        ownSliceCap V s' (DFrac.own 1) }} := by
  wp_start as ⟨Hs, Hcap⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hs
  wp_apply wp_sumAssumeNoOverflowSigned with %Hoverflow
  have hA1 : a + W64 1 - W64 0 = a + W64 1 := by word
  have hC : sl.cap - W64 0 = sl.cap := by word
  have hN2 : a + W64 1 + (sl.len - a) = sl.len + W64 1 := by word
  simp only [hA1, hC, hN2] at Hoverflow ⊢
  have hL1 : sint.Z (sl.len + W64 1) = sint.Z sl.len + 1 := by
    have := ha.2; word
  wp_if_destruct
  · try simp only [hC] at Hif ⊢
    rw [ite_eq_left ⟨by decide, by word, Hif⟩]
    rw [slice_slice sl (W64 0) (a + W64 1) (W64 0) (sl.len + W64 1) (by word)]
    simp only [show ∀ x : w64, W64 0 + x = x from fun x => by word]
    wp_auto
    try simp only [hA1, hC] at Hif ⊢
    rw [ite_eq_left ⟨by word, by word, Hif⟩]
    -- the source `s[a:]` as a part of `X = s[:len+1]`
    have hsrc : slice.slice sl V a sl.len =
        slice.slice (slice.slice sl V (W64 0) (sl.len + W64 1)) V a sl.len := by
      rw [slice_slice sl (W64 0) (sl.len + W64 1) a sl.len (by word)]
      simp only [show ∀ x : w64, W64 0 + x = x from fun x => by word]
    rw [hsrc]
    -- `X`'s elements: `s`'s and one slot of its capacity
    icases ownSliceCap_split (V := V) (sl.len + W64 1) sl $$ [Hcap] with ⟨%vs', Hs', Hcap⟩
    · iframe Hcap; ipureintro; constructor <;> word
    ihave %Hlen' := ownSlice_len _ _ _ $$ Hs'
    ihave HX := ownSlice_combine sl.len sl _ vs vs' (W64 0) (sl.len + W64 1)
      ⟨by word, by word, by word, by word⟩ $$ [Hs] Hs'
    · iapply (ownSlice_trivial_slice sl _ vs).1 $$ Hs
    have hXl : (slice.slice sl V (W64 0) (sl.len + W64 1)).len = sl.len + W64 1 := by
      simp only [slice.slice]; word
    have hb1 : 0 ≤ sint.Z (a + W64 1) ∧ sint.Z (a + W64 1) ≤ sint.Z (sl.len + W64 1) ∧
        sint.Z (sl.len + W64 1) ≤ sint.Z (slice.slice sl V (W64 0) (sl.len + W64 1)).len := by
      rw [hXl]; have := ha.2; refine ⟨by word, by word, Int.le_refl _⟩
    have hb2 : 0 ≤ sint.Z a ∧ sint.Z a ≤ sint.Z sl.len ∧
        sint.Z sl.len ≤ sint.Z (slice.slice sl V (W64 0) (sl.len + W64 1)).len := by
      rw [hXl]; refine ⟨ha.1, by word, by word⟩
    wp_apply (wp_slice_copy_within (V := V) (slice.slice sl V (W64 0) (sl.len + W64 1)) (vs ++ vs')
      (a + W64 1) (sl.len + W64 1) a sl.len hb1 hb2) $$ [$HX] as %n ⟨-, HX⟩
    iapply HΦ
    have hna : sint.nat (a + W64 1) = sint.nat a + 1 := by have := ha.2; word
    have hnl : sint.nat (sl.len + W64 1) = sint.nat sl.len + 1 := by have := ha.2; word
    rw [hna, hnl, list_shift_within vs vs' (sint.nat a) (sint.nat sl.len) Hlen.1
      (by rw [Hlen'.1]; simp only [slice.slice]; word) (by word)]
    iframe HX
    iapply ownSliceCap_slice_change_first sl sl.len (W64 0) (sl.len + W64 1) _
      ⟨Hif, by word, by word, by word, by word⟩ $$ Hcap
  · wp_apply wp_new_cap with %cap %Hcap_ge
    wp_apply wp_slice_make3 (V := V) (sl.len + W64 1) cap ⟨by word, Hcap_ge⟩
      with %nsl ⟨Hnew, Hnew_cap, %Hcap⟩
    ihave %Hnl := ownSlice_len _ _ _ $$ Hnew
    simp only [List.length_replicate] at Hnl
    -- `copy(s_new, s[:a+1])`
    icases (ownSlice_slice (W64 0) (a + W64 1) sl _ vs ⟨by decide, by word, by word⟩).1 $$ Hs
      with ⟨H1, H2, H3⟩
    wp_apply wp_slice_copy nsl _ _ _ (DFrac.own 1) $$ [Hnew H2] with %n' ⟨%Hn', Hnew, H2⟩
    · iframe Hnew H2
    ihave Hs := (ownSlice_slice (W64 0) (a + W64 1) sl _ vs ⟨by decide, by word, by word⟩).2
      $$ [H1 H2 H3]
    · iframe H1 H2 H3
    try wp_auto
    have hna : sint.nat (a + W64 1) = sint.nat a + 1 := by have := ha.2; word
    have hnl : sint.nat (sl.len + W64 1) = sint.nat sl.len + 1 := by have := ha.2; word
    have h0 : sint.nat (W64 0) = 0 := rfl
    have hil : sint.nat a < vs.length := by rw [Hlen.1]; word
    have hL : (subslice 0 (sint.nat a + 1) vs).take
          (List.replicate (sint.nat sl.len + 1) (zero_val V)).length ++
        (List.replicate (sint.nat sl.len + 1) (zero_val V)).drop
          (subslice 0 (sint.nat a + 1) vs).length =
        vs.take (sint.nat a + 1) ++ List.replicate (sint.nat sl.len - sint.nat a) (zero_val V) := by
      have hs0 : subslice 0 (sint.nat a + 1) vs = vs.take (sint.nat a + 1) := by
        simp [subslice]
      rw [hs0, List.length_replicate, List.length_take, List.drop_replicate,
        List.take_of_length_le (by rw [List.length_take]; omega)]
      congr 2; omega
    rw [hna, hnl, h0, hL]
    simp only [hA1]
    rw [ite_eq_left ⟨by word, by word, by rw [Hcap]; exact Hcap_ge⟩]
    have hnslen : nsl.len = sl.len + W64 1 := by have := Hnl.1; have := ha.2; word
    -- `copy(s_new[a+1:], s[a:])`
    icases (ownSlice_slice (a + W64 1) (sl.len + W64 1) nsl _ _
      ⟨by word, by have := ha.2; word, by rw [hnslen]; exact Int.le_refl _⟩).1 $$ Hnew
      with ⟨N1, N2, -⟩
    icases (ownSlice_slice a sl.len sl _ vs ⟨ha.1, by word, Int.le_refl _⟩).1 $$ Hs
      with ⟨-, S2, -⟩
    wp_apply wp_slice_copy _ _ _ _ (DFrac.own 1) $$ [N2 S2] with %n'' ⟨-, N2, -⟩
    · iframe N2 S2
    try wp_auto
    iapply HΦ
    iframe Hnew_cap
    rw [hna, hnl]
    have hsub : subslice (sint.nat a) (sint.nat sl.len) vs = vs.drop (sint.nat a) := by
      simp [subslice, ← Hlen.1]
    have hlen2 : (subslice (sint.nat a + 1) (sint.nat sl.len + 1)
        (List.take (sint.nat a + 1) vs ++
          List.replicate (sint.nat sl.len - sint.nat a) (zero_val V))).length =
        sint.nat sl.len - sint.nat a := by
      simp only [subslice, List.length_drop, List.length_take, List.length_append,
        List.length_replicate]; omega
    have hdl : (vs.drop (sint.nat a)).length = sint.nat sl.len - sint.nat a := by
      rw [List.length_drop]; omega
    have hA : (vs.drop (sint.nat a)).take (subslice (sint.nat a + 1) (sint.nat sl.len + 1)
        (List.take (sint.nat a + 1) vs ++
          List.replicate (sint.nat sl.len - sint.nat a) (zero_val V))).length =
        vs.drop (sint.nat a) := List.take_of_length_le (by rw [hlen2, hdl]; exact Nat.le_refl _)
    have hB : (subslice (sint.nat a + 1) (sint.nat sl.len + 1)
        (List.take (sint.nat a + 1) vs ++
          List.replicate (sint.nat sl.len - sint.nat a) (zero_val V))).drop
          (vs.drop (sint.nat a)).length = [] :=
      List.drop_of_length_le (by rw [hlen2, hdl]; exact Nat.le_refl _)
    have hC1 : (List.take (sint.nat a + 1) vs ++
          List.replicate (sint.nat sl.len - sint.nat a) (zero_val V)).take (sint.nat a + 1) =
        vs.take (sint.nat a + 1) := List.take_left' (by rw [List.length_take]; omega)
    rw [hsub, hA, hB, List.append_nil, hC1]
    ihave H := ownSlice_combine (a + W64 1) nsl _ (vs.take (sint.nat a + 1)) (vs.drop (sint.nat a))
      (W64 0) (sl.len + W64 1)
      ⟨by rw [List.length_take, hna, h0]; omega, by decide, by word, by have := ha.2; word⟩ $$ N1 N2
    rw [← hnslen]
    iapply (ownSlice_trivial_slice nsl _ _).2 $$ H


end wps

end Perennial
