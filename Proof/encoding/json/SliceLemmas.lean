/-
Slice lemmas for the encoding/json model's `Decoder.fetch` (`Codec/Decoder__fetch_conn.lean`):

* `wp_slice_copy_within_int`: `copy(s[a:b], s[c:d])` within one slice with the count as a signed integer: Perennial's
`wp_slice_copy_within` (`Perennial/Golang/Theory/Slice.lean`) gives the count as `sint.nat n`
only, which says nothing of its sign when it is `0`; the encoding/json model's `Decoder.fetch`
then slices with it (`dec.buf[:n]`), which needs `0 ≤ n`. Its proof, with the count of the second
`copyForward` kept as `sint.Z n` (`wp_copyForward` gives it). Local until Perennial's lemma says it
(`notes/perennial-changes.md`, 2026-11-25, "`copy` within one slice");
* `ownSliceCap_restore`: the free space `s[len:cap]` and its capacity are `s`'s capacity again (what
  `fetch` keeps when a `Read` into the free space returns no byte).
-/
module

public import Perennial.Golang.Theory.Slice

@[expose] public section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace encoding.json

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [preSem : go.PreSemantics]
variable {s : Stuckness} {E : CoPset}
variable {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]

/-- `wp_slice_copy_within` with the count's sign (see the file header). -/
theorem wp_slice_copy_within_int {st t : go.GoType} [st ↓u go.SliceType t]
    [IntoValTyped (GF := GF) V t] (sl : GoSlice) (vs : List V) (a b c d : w64)
    (hab : 0 ≤ sint.Z a ∧ sint.Z a ≤ sint.Z b ∧ sint.Z b ≤ sint.Z sl.len)
    (hcd : 0 ≤ sint.Z c ∧ sint.Z c ≤ sint.Z d ∧ sint.Z d ≤ sint.Z sl.len) :
    {{ (sl ↦* vs : IProp GF) }}
      (App (App (Val #(functions go.copy [st])) (Val #(slice.slice sl V a b)))
        (Val #(slice.slice sl V c d))) @ s; E
    {{ (n : w64), RET #n;
        ⌜sint.Z n = min ((sint.nat b - sint.nat a : Nat) : Int) ((sint.nat d - sint.nat c : Nat) : Int)⌝ ∗
        sl ↦* (vs.take (sint.nat a) ++
          ((subslice (sint.nat c) (sint.nat d) vs).take (sint.nat b - sint.nat a) ++
            (subslice (sint.nat a) (sint.nat b) vs).drop (sint.nat d - sint.nat c)) ++
          vs.drop (sint.nat b)) }} := by
  wp_start as Hs
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  icases (ownSlice_slice c d sl _ vs hcd).1 $$ Hs with ⟨Hc1, Hc2, Hc3⟩
  ihave %Hlenc := ownSlice_len _ _ _ $$ Hc2
  simp only [slice.slice] at Hlenc
  wp_apply wp_slice_make2 (V := V) (d - c) $$ [] as %tmp ⟨Htmp, _⟩
  · ipureintro; exact Hlenc.2
  wp_apply wp_copyForward tmp _ _ _ (DFrac.own 1) $$ [Htmp Hc2] as %n1 ⟨_, Htmp, Hc2⟩
  · iframe
  have e : ∀ l : List V, l.length = sint.nat (d - c) →
      l.take (List.replicate (sint.nat (d - c)) (zero_val V)).length ++
      (List.replicate (sint.nat (d - c)) (zero_val V)).drop l.length = l := by
    intro l hl
    rw [List.length_replicate, ← hl, List.take_length, List.drop_replicate, Nat.sub_self,
      List.replicate_zero, List.append_nil]
  rw [e _ Hlenc.1]
  ihave Hs := (ownSlice_slice c d sl _ vs hcd).2 $$ [Hc1 Hc2 Hc3]
  · iframe
  icases (ownSlice_slice a b sl _ vs hab).1 $$ Hs with ⟨Ha1, Ha2, Ha3⟩
  wp_apply wp_copyForward _ _ tmp _ (DFrac.own 1) $$ [Ha2 Htmp] as %n ⟨%Hn, Ha2, _⟩
  · iframe
  iapply HΦ
  have hla : (subslice (sint.nat a) (sint.nat b) vs).length = sint.nat b - sint.nat a := by
    simp only [subslice, List.length_drop, List.length_take]; word
  have hlc : (subslice (sint.nat c) (sint.nat d) vs).length = sint.nat d - sint.nat c := by
    simp only [subslice, List.length_drop, List.length_take]; word
  rw [hla, hlc] at Hn ⊢
  isplitr
  · ipureintro; rw [Hn]; omega
  have hlt : (vs.take (sint.nat a)).length = sint.nat a := by
    simp only [List.length_take]; word
  have hmid : ((subslice (sint.nat c) (sint.nat d) vs).take (sint.nat b - sint.nat a) ++
      (subslice (sint.nat a) (sint.nat b) vs).drop (sint.nat d - sint.nat c)).length =
      sint.nat b - sint.nat a := by
    simp only [List.length_append, List.length_take, List.length_drop, hla, hlc]; omega
  iapply (ownSlice_slice a b sl _ _ hab).2
  obtain ⟨h1, h2, h3⟩ := list_slice3 (vs.take (sint.nat a)) _ (vs.drop (sint.nat b)) _ _ hlt hmid
    (by word)
  rw [h1, h2, h3]
  iframe

include preSem in
/-- The free space `s[len:cap]`, held, and its capacity are `s`'s capacity. -/
theorem ownSliceCap_restore (s : GoSlice) (vs : List V)
    (hs : 0 ≤ sint.Z s.len ∧ sint.Z s.len ≤ sint.Z s.cap) :
    (slice.slice s V s.len s.cap ↦* vs ∗ ownSliceCap V (slice.slice s V s.len s.cap) (DFrac.own 1) :
      IProp GF) ⊢ ownSliceCap V s (DFrac.own 1) := by
  iintro ⟨Hvs, Hcap⟩
  have hl : (slice.slice s V s.len s.cap).len = s.cap - s.len := rfl
  have hc : (slice.slice s V s.len s.cap).cap = s.cap - s.len := rfl
  have hz : sint.Z (s.cap - s.len) = sint.Z s.cap - sint.Z s.len := by word
  have h00 : sint.Z (W64 0) = 0 := rfl
  ihave Hvs := (ownSlice_trivial_slice _ _ _).1 $$ Hvs
  ihave H := ownSlice_slice_absorb_capacity (slice.slice s V s.len s.cap) vs (W64 0) (W64 0)
    ⟨Int.le_refl _, Int.le_refl _, by rw [h00, hl, hz]; omega⟩ $$ [Hvs Hcap]
  · rw [show slice.slice (slice.slice s V s.len s.cap) V (W64 0)
        (slice.slice s V s.len s.cap).len = slice.slice s V s.len s.cap from
        (slice_slice_trivial _).symm]
    iframe
  have hov : 0 ≤ sint.Z s.len + sint.Z (W64 0) ∧ sint.Z s.len + sint.Z (W64 0) < 2 ^ 63 := by
    rw [h00]; constructor <;> word
  rw [slice_slice s s.len s.cap (W64 0) (W64 0) hov, show s.len + W64 0 = s.len by word]
  ihave H := ownSliceCap_slice_change_first s s.len (W64 0) s.len _
    ⟨hs.2, hs.1, Int.le_refl _, Int.le_refl _, hs.1⟩ $$ H
  rw [show slice.slice s V (W64 0) s.len = s from (slice_slice_trivial s).symm]
  iexact H

end wps

end encoding.json
end Perennial
