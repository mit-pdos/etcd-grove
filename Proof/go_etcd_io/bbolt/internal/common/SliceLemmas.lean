/-
`append` within capacity, in place: Perennial's `wp_slice_append` returns some slice
`s'`, which may be a new array; `Mergepgids` is correct only because its appends onto
`dst[:0]` stay inside `dst`. Within capacity, Go's `append(s, s2...)` is
`s[0:len(s)+len(s2)]` with `s2` copied to `[len(s), len(s)+len(s2))`, and it touches
only that range of the capacity, so only that range has to be owned.
-/
module

public import Perennial.Golang.Theory.Slice

@[expose] public section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [preSem : go.PreSemantics]
variable {s : Stuckness} {E : CoPset}
variable {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]

/-- `append(sl, sl2...)` with room in `sl`'s capacity: the result is
`sl[0:len(sl)+len(sl2)]`, and the call needs (and writes) only the range
`sl[len(sl):len(sl)+len(sl2)]` of the capacity, whatever it holds (`junk`). -/
theorem wp_slice_append_in_place {st t : go.GoType} [st ↓u go.SliceType t]
    [IntoValTyped (GF := GF) V t]
    (sl : GoSlice) (vs : List V) (junk : List V) (sl2 : GoSlice) (vs' : List V) (dq : DFrac)
    (hcap : sint.Z sl.len + sint.Z sl2.len ≤ sint.Z sl.cap) :
    {{ (sl ↦* vs ∗ slice.slice sl V sl.len (sl.len + sl2.len) ↦* junk ∗
        sl2 ↦*{dq} vs' : IProp GF) }}
      (App (App (Val #(functions go.append [st])) (Val #sl)) (Val #sl2)) @ s; E
    {{ RET #(slice.slice sl V (W64 0) (sl.len + sl2.len));
        slice.slice sl V (W64 0) (sl.len + sl2.len) ↦* (vs ++ vs') ∗ sl2 ↦*{dq} vs' }} := by
  wp_start as ⟨Hs, Hjunk, Hs2⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  ihave %Hlen2 := ownSlice_len _ _ _ $$ Hs2
  ihave %Hwf1 := ownSlice_wf _ _ _ $$ Hs
  ihave %Hwf2 := ownSlice_wf _ _ _ $$ Hs2
  wp_apply wp_sumAssumeNoOverflowSigned with %Hoverflow
  wp_if_destruct
  · rw [ite_eq_left ⟨by word, by word, Hif⟩]
    wp_auto
    rw [ite_eq_left (by (try simp only [slice.slice]); word)]
    wp_auto
    rw [slice_slice sl (W64 0) (sl.len + sl2.len) sl.len (sl.len + sl2.len) (by word)]
    have h0 : ∀ x : w64, W64 0 + x = x := fun x => by word
    simp only [h0]
    ihave %Hlen3 := ownSlice_len _ _ _ $$ Hjunk
    wp_apply +noauto wp_slice_copy _ _ sl2 vs' dq $$ [Hjunk Hs2] with %n ⟨%Hn, Hs_new, Hs2⟩
    · iframe Hjunk Hs2
    have hd : junk.length = vs'.length := by
      rw [Hlen3.1]; simp only [slice.slice]; word
    rw [hd, List.take_length, List.drop_of_length_le (l := junk) (i := vs'.length) (by omega),
      List.append_nil]
    wp_auto
    iapply HΦ
    iframe Hs2
    iapply ownSlice_combine sl.len sl _ vs vs' (W64 0) (sl.len + sl2.len)
      ⟨by word, by word, by word, by word⟩ $$ [Hs] Hs_new
    iapply (ownSlice_trivial_slice sl _ vs).1 $$ Hs
  · exfalso; apply Hif; word

theorem slice_prefix_len (sl : GoSlice) (n : w64) : (slice.slice sl V (W64 0) n).len = n := by
  simp only [slice.slice]; word

/-- `wp_slice_append_in_place` for a prefix `dst[0:k]` of a slice, appending `n` elements
into `dst[k:k+n]`: the result is `dst[0:k+n]`. -/
theorem wp_slice_append_prefix {st t : go.GoType} [st ↓u go.SliceType t]
    [IntoValTyped (GF := GF) V t]
    (dst : GoSlice) (k : w64) (vs : List V) (junk : List V) (sl2 : GoSlice) (vs' : List V)
    (dq : DFrac) (n : w64) (hn : sl2.len = n)
    (hk : 0 ≤ sint.Z k) (hcap : sint.Z k + sint.Z n ≤ sint.Z dst.cap) :
    {{ (slice.slice dst V (W64 0) k ↦* vs ∗ slice.slice dst V k (k + n) ↦* junk ∗
        sl2 ↦*{dq} vs' : IProp GF) }}
      (App (App (Val #(functions go.append [st])) (Val #(slice.slice dst V (W64 0) k)))
        (Val #sl2)) @ s; E
    {{ RET #(slice.slice dst V (W64 0) (k + n));
        slice.slice dst V (W64 0) (k + n) ↦* (vs ++ vs') ∗ sl2 ↦*{dq} vs' }} := by
  subst hn
  iintro %Φ ⟨Hs, Hjunk, Hs2⟩ HΦ
  have hl := slice_prefix_len (V := V) dst k
  have hss : slice.slice (slice.slice dst V (W64 0) k) V k (k + sl2.len) =
      slice.slice dst V k (k + sl2.len) := by
    rw [slice_slice dst (W64 0) k k (k + sl2.len) (by word)]
    simp only [show ∀ x : w64, W64 0 + x = x from fun x => by word]
  have hs0 : slice.slice (slice.slice dst V (W64 0) k) V (W64 0) (k + sl2.len) =
      slice.slice dst V (W64 0) (k + sl2.len) := by
    rw [slice_slice dst (W64 0) k (W64 0) (k + sl2.len) (by word)]
    simp only [show ∀ x : w64, W64 0 + x = x from fun x => by word]
  have hc : (slice.slice dst V (W64 0) k).cap = dst.cap := by simp only [slice.slice]; word
  iapply wp_slice_append_in_place (slice.slice dst V (W64 0) k) vs junk sl2 vs' dq
    (by rw [hl, hc]; exact hcap) $$ [Hs Hjunk Hs2]
  · rw [hl, hss]; iframe
  · rw [hl, hs0]; iexact HΦ

end wps

end Perennial
