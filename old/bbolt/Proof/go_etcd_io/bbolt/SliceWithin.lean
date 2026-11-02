/-
`append` within one slice: `append(s[:i], s[i+1:]...)`, Go's idiom for deleting element `i`
(`node.del`, `node.removeChild`). Perennial's `wp_slice_append` needs the destination's
capacity and the appended slice owned separately, which they are not here (the capacity of
`s[:i]` is the rest of `s`); the append happens in place (the capacity of `s[:i]` is that of
`s`), as a copy within `s` (`wp_slice_copy_within`).
-/
module

public import Perennial.Golang.Theory

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode

theorem delete_copy_list {A : Type} (vs : List A) (a : Nat) (ha : a < vs.length) :
    vs.take a ++ ((subslice (a + 1) vs.length vs).take (vs.length - 1 - a) ++
      (subslice a (vs.length - 1) vs).drop (vs.length - (a + 1))) ++ vs.drop (vs.length - 1) =
    (vs.take a ++ vs.drop (a + 1)) ++ vs.drop (vs.length - 1) := by
  have h1 : subslice (a + 1) vs.length vs = vs.drop (a + 1) := by
    simp only [subslice, List.take_length]
  have h2 : (subslice a (vs.length - 1) vs).drop (vs.length - (a + 1)) = [] := by
    apply List.drop_of_length_le
    simp [subslice]; omega
  rw [h1, h2, List.append_nil,
    List.take_of_length_le (l := List.drop (a + 1) vs) (i := vs.length - 1 - a) (by simp; omega)]

theorem delete_list_length {A : Type} (vs : List A) (a : Nat) (ha : a < vs.length) :
    (vs.take a ++ vs.drop (a + 1)).length = vs.length - 1 := by
  simp only [List.length_append, List.length_take, List.length_drop]; omega

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [preSem : go.PreSemantics]
variable {stk : Stuckness} {E : CoPset}
variable {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]

/-- `append(s[:i], s[i+1:]...)`: `s` without its element `i`, in place (the old last cell
goes back to the capacity). -/
theorem wp_slice_append_delete {st t : go.GoType} [st ↓u go.SliceType t]
    [IntoValTyped (GF := GF) V t] (s : GoSlice) (vs : List V) (i : w64)
    (hi : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z s.len) :
    {{ (s ↦* vs ∗ ownSliceCap V s (DFrac.own 1) : IProp GF) }}
      (App (App (Val #(functions go.append [st])) (Val #(slice.slice s V (W64 0) i)))
        (Val #(slice.slice s V (i + W64 1) s.len))) @ stk; E
    {{ RET #(slice.slice s V (W64 0) (s.len - W64 1));
        slice.slice s V (W64 0) (s.len - W64 1) ↦* (vs.take (sint.nat i) ++ vs.drop (sint.nat i + 1)) ∗
        ownSliceCap V (slice.slice s V (W64 0) (s.len - W64 1)) (DFrac.own 1) }} := by
  wp_start as ⟨Hs, Hcap⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  ihave %Hcw := ownSliceCap_wf _ _ $$ Hcap
  wp_apply wp_sumAssumeNoOverflowSigned with %Hoverflow
  wp_if_destruct
  · rw [ite_eq_left ⟨by word, by (try simp only [slice.slice]); word, Hif⟩]
    wp_auto
    rw [ite_eq_left (by (try simp only [slice.slice]); word)]
    wp_auto
    have Hn : sint.nat s.len = vs.length := Hlen.1.symm
    have e2 : slice.slice (slice.slice s V (W64 0) i) V (W64 0) (i - W64 0 + (s.len - (i + W64 1))) =
        slice.slice s V (W64 0) (s.len - W64 1) := by
      rw [slice_slice s (W64 0) i (W64 0) _ (by word),
        show W64 0 + W64 0 = W64 0 by word,
        show W64 0 + (i - W64 0 + (s.len - (i + W64 1))) = s.len - W64 1 by word]
    have e1 : slice.slice (slice.slice s V (W64 0) (s.len - W64 1)) V (i - W64 0)
        (i - W64 0 + (s.len - (i + W64 1))) = slice.slice s V i (s.len - W64 1) := by
      rw [slice_slice s (W64 0) (s.len - W64 1) (i - W64 0) _ (by word),
        show W64 0 + (i - W64 0) = i by word,
        show W64 0 + (i - W64 0 + (s.len - (i + W64 1))) = s.len - W64 1 by word]
    rw [e2, e1]
    wp_apply wp_slice_copy_within s vs i (s.len - W64 1) (i + W64 1) s.len
      ⟨hi.1, by word, by word⟩ ⟨by word, by word, by word⟩ $$ [Hs] as %n ⟨_, Hs⟩
    · iframe
    have ha : sint.nat i < vs.length := by word
    rw [show sint.nat (s.len - W64 1) = vs.length - 1 by word,
      show sint.nat (i + W64 1) = sint.nat i + 1 by word, Hn,
      show vs.length - 1 - sint.nat i = vs.length - 1 - sint.nat i from rfl,
      delete_copy_list vs (sint.nat i) ha]
    icases (ownSlice_split_all (s.len - W64 1) s _ _ ⟨by word, by word⟩).1 $$ Hs with ⟨H1, H2⟩
    have hl := delete_list_length vs (sint.nat i) ha
    rw [show sint.nat (s.len - W64 1) = vs.length - 1 by word, ← hl, List.take_left, List.drop_left]
    ihave Hc := ownSlice_slice_absorb_capacity s _ (W64 0) (s.len - W64 1)
      ⟨by decide, by word, by word⟩ $$ [H2 Hcap]
    · iframe
    iapply HΦ
    iframe
  · exfalso; apply Hif; (try simp only [slice.slice]); word

end wps

end bbolt
end EtcdGrove
end Perennial
