/-
Facts about Perennial's slices that belong to no Go package: Go's idiom for deleting the `i`th
element of a slice in place, `append(s[:i], s[i+1:]...)` (`client/v3`'s `keepAliveCtxCloser`).

Kept here until Perennial has it: a candidate for an independent Perennial proposal (CLAUDE.md,
"Changes to Perennial"; `notes/decisions.md`, "Proof/Lib: facts that belong to no Go package").
-/
module

public import Perennial.Golang.Theory.Slice

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

/-- The list `copy(s[i:len-1], s[i+1:len])` leaves, cut to `len - 1`: `vs` without its `i`th
element. -/
theorem subslice_delete_eq {V : Type} (vs : List V) (k : Nat) (hk : k < vs.length) :
    subslice 0 (vs.length - 1) (vs.take k ++
      ((subslice (k + 1) vs.length vs).take (vs.length - 1 - k) ++
        (subslice k (vs.length - 1) vs).drop (vs.length - (k + 1))) ++
      vs.drop (vs.length - 1)) = vs.eraseIdx k := by
  have h1 : (subslice (k + 1) vs.length vs).take (vs.length - 1 - k) = vs.drop (k + 1) := by
    simp only [subslice, List.take_length]
    apply List.take_of_length_le
    simp; omega
  have h2 : (subslice k (vs.length - 1) vs).drop (vs.length - (k + 1)) = [] := by
    simp only [subslice]
    apply List.drop_of_length_le
    simp; omega
  rw [h1, h2, List.append_nil, ← List.eraseIdx_eq_take_drop_succ]
  simp only [subslice, List.drop_zero]
  rw [List.take_append_of_le_length (by rw [List.length_eraseIdx_of_lt hk]; omega)]
  rw [List.take_of_length_le (by rw [List.length_eraseIdx_of_lt hk]; omega)]

section slice
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [preSem : go.PreSemantics]
variable {s : Stuckness} {E : CoPset}
variable {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]

set_option maxHeartbeats 1000000 in
/-- **`append(s[:i], s[i+1:]...)`**, Go's in-place deletion of the `i`th element: the slice
without it, with the capacity (the old last cell moves into it). -/
theorem wp_slice_delete {st t : go.GoType} [st ↓u go.SliceType t] [IntoValTyped (GF := GF) V t]
    (sl : GoSlice) (vs : List V) (i : w64)
    (hi : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len) :
    {{ (sl ↦* vs ∗ ownSliceCap V sl (DFrac.own 1) : IProp GF) }}
      (App (App (Val #(functions go.append [st])) (Val #(slice.slice sl V (W64 0) i)))
        (Val #(slice.slice sl V (i + W64 1) sl.len))) @ s; E
    {{ (s' : GoSlice), RET #s';
        s' ↦* vs.eraseIdx (sint.nat i) ∗ ownSliceCap V s' (DFrac.own 1) }} := by
  wp_start as ⟨Hs, Hcap⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hs
  ihave %Hcwf := ownSliceCap_wf _ _ $$ Hcap
  wp_apply wp_sumAssumeNoOverflowSigned with %Hoverflow
  have hnl : i - W64 0 + (sl.len - (i + W64 1)) = sl.len - W64 1 := by word
  have hc0 : sl.cap - W64 0 = sl.cap := by word
  rw [hnl, hc0, decide_eq_true (by word : sint.Z (sl.len - W64 1) ≤ sint.Z sl.cap)]
  wp_auto
  rw [ite_eq_left (by rw [hc0]; constructor <;> word)]
  have hss : slice.slice (slice.slice sl V (W64 0) i) V (W64 0) (sl.len - W64 1) =
      slice.slice sl V (W64 0) (sl.len - W64 1) := by
    rw [slice_slice sl (W64 0) i (W64 0) (sl.len - W64 1) (by word)]
    congr 1 <;> word
  rw [hss]
  wp_auto
  rw [ite_eq_left (by rw [hc0]; constructor <;> word)]
  have hss2 : slice.slice (slice.slice sl V (W64 0) (sl.len - W64 1)) V (i - W64 0) (sl.len - W64 1) =
      slice.slice sl V i (sl.len - W64 1) := by
    rw [slice_slice sl (W64 0) (sl.len - W64 1) (i - W64 0) (sl.len - W64 1) (by word)]
    congr 1 <;> word
  rw [hss2]
  wp_apply (wp_slice_copy_within sl vs i (sl.len - W64 1) (i + W64 1) sl.len
    ⟨hi.1, by word, by word⟩ ⟨by word, by word, by word⟩) $$ [$Hs] as %n ⟨%Hn, Hs⟩
  ihave ⟨-, Hs', Hcap'⟩ := ownSlice_slice_with_cap (W64 0) (sl.len - W64 1) sl _
    ⟨by word, by word, by word⟩ $$ [$Hs $Hcap]
  iapply HΦ
  iframe Hcap'
  have hL : sint.nat sl.len = vs.length := Hlen.1.symm
  have hL1 : sint.nat (sl.len - W64 1) = vs.length - 1 := by word
  have hk1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
  have hk : sint.nat i < vs.length := by word
  iExactEq Hs'
  rw [hL1, hk1, hL, show sint.nat (W64 0) = 0 from rfl, subslice_delete_eq vs (sint.nat i) hk]

end slice

end EtcdGrove
end Perennial
