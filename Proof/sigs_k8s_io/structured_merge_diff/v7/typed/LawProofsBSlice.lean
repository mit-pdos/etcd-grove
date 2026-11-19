/-
**`append` with a way back from any contents** (the reconcile walker's `prepareDescent`): Perennial's
`wp_slice_append_undo` gives the old slice back from the new one holding exactly the appended
contents; a child walker may give its path buffer back with other elements of the same length
(another representation of the same path), so the way back here takes any contents of the new
slice's length, and gives the old slice with its old contents (`append` reallocated) or the new
contents' prefix (`append` wrote in place).
-/
module

public import Perennial.Golang.Theory.Slice

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [preSem : go.PreSemantics]
variable {s : Stuckness} {E : CoPset}
variable {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]

theorem wp_slice_append_undo_any {st t : go.GoType} [st ↓u go.SliceType t]
    [IntoValTyped (GF := GF) V t]
    (sl : GoSlice) (vs : List V) (sl2 : GoSlice) (vs' : List V) (dq : DFrac) :
    {{ (sl ↦* vs ∗ ownSliceCap V sl (DFrac.own 1) ∗ sl2 ↦*{dq} vs' : IProp GF) }}
      (App (App (Val #(functions go.append [st])) (Val #sl)) (Val #sl2)) @ s; E
    {{ (s' : GoSlice), RET #s';
        s' ↦* (vs ++ vs') ∗ ownSliceCap V s' (DFrac.own 1) ∗ sl2 ↦*{dq} vs' ∗
        (∀ vs2 : List V, s' ↦* vs2 ∗ ownSliceCap V s' (DFrac.own 1) -∗
          ∃ vs1 : List V, sl ↦* vs1 ∗ ownSliceCap V sl (DFrac.own 1) ∗
            ⌜vs1 = vs ∨ vs1 = vs2.take vs.length⌝) }} := by
  wp_start_folded as ⟨Hs, Hcap, Hs2⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  ihave %Hlen2 := ownSlice_len _ _ _ $$ Hs2
  ihave %Hwf1 := ownSlice_wf _ _ _ $$ Hs
  by_cases hfit : sint.Z sl.len + sint.Z sl2.len ≤ sint.Z sl.cap
  · iapply wp_slice_append_fits sl sl2 _ ⟨Hlen.2, Hlen2.2⟩ hfit
    icases ownSliceCap_split (V := V) (sl.len + sl2.len) sl $$ [Hcap] with ⟨%vs'', Hs_new, Hcap⟩
    · iframe Hcap; ipureintro; constructor <;> word
    ihave %Hlen3 := ownSlice_len _ _ _ $$ Hs_new
    wp_apply +noauto wp_slice_copy _ _ sl2 vs' dq $$ [Hs_new Hs2] with %n ⟨%Hn, Hs_new, Hs2⟩
    · iframe Hs_new Hs2
    have hd : vs''.length = vs'.length := by
      rw [Hlen3.1]; simp only [slice.slice]; word
    rw [hd, List.take_length, List.drop_of_length_le (l := vs'') (i := vs'.length) (by omega),
      List.append_nil]
    isplitl []
    · ipureintro; exact isPanic_intoVal _
    imodintro
    iapply HΦ
    iframe Hs2
    isplitl [Hs Hs_new]
    · iapply ownSlice_combine sl.len sl _ vs vs' (W64 0) (sl.len + sl2.len)
        ⟨by word, by word, by word, by word⟩ $$ [Hs] Hs_new
      iapply (ownSlice_trivial_slice sl _ vs).1 $$ Hs
    isplitl [Hcap]
    · iapply ownSliceCap_slice_change_first sl sl.len (W64 0) (sl.len + sl2.len) _
        ⟨by word, by word, by word, by word, by word⟩ $$ Hcap
    · iintro %vs2 ⟨Hn, Hc⟩
      ihave %Hl2 := ownSlice_len _ _ _ $$ Hn
      have hsplit : vs2 = vs2.take vs.length ++ vs2.drop vs.length :=
        (List.take_append_drop _ _).symm
      have hle : vs.length ≤ vs2.length := by
        rw [Hl2.1]; simp only [slice.slice]; rw [Hlen.1]; word
      have htl : (vs2.take vs.length).length = sint.nat sl.len := by
        rw [List.length_take]
        rw [Nat.min_eq_left hle, Hlen.1]
      rw [hsplit]
      iexists vs2.take vs.length
      ihave H := ownSlice_append_undo_in_place sl (vs2.take vs.length) (vs2.drop vs.length)
        (sl.len + sl2.len) ⟨Hlen.2, by word, by word⟩ htl $$ [Hn Hc]
      · iframe Hn Hc
      icases H with ⟨H1, H2⟩
      iframe H1 H2
      ipureintro; right
      rw [List.take_append_of_le_length (by rw [List.length_take, Nat.min_eq_left hle]; exact Nat.le_refl _), List.take_take,
        Nat.min_self]
  · iapply wp_slice_append_grow sl sl2 _ ⟨Hlen.2, Hlen2.2⟩ (by omega)
    iintro %nsl %Hoverflow Hnew Hnew_cap
    ihave %Hsl_len := ownSlice_len _ _ _ $$ Hnew
    simp only [List.length_replicate] at Hsl_len
    wp_apply wp_slice_copy nsl _ sl vs (DFrac.own 1) $$ [Hnew Hs] with %n' ⟨%Hn', Hnew, Hs⟩
    · iframe Hnew Hs
    isplitl []
    · ipureintro; exact isPanic_intoVal _
    icases (ownSlice_slice sl.len (sl.len + sl2.len) nsl _ _ ⟨by word, by word, by word⟩).1 $$ Hnew
      with ⟨Hnew1, Hnew2, _⟩
    wp_apply +noauto wp_slice_copy _ _ sl2 vs' dq $$ [Hnew2 Hs2] with %n'' ⟨%Hn'', Hnew2, Hs2⟩
    · iframe Hnew2 Hs2
    have hN : sint.nat (sl.len + sl2.len) = vs.length + vs'.length := by word
    have ha : (vs.take (List.replicate (sint.nat (sl.len + sl2.len)) (zero_val V)).length ++
        (List.replicate (sint.nat (sl.len + sl2.len)) (zero_val V)).drop vs.length).take
          (sint.nat sl.len) = vs := by
      rw [List.length_replicate, List.take_of_length_le (l := vs) (i := sint.nat (sl.len + sl2.len)) (by omega),
        show sint.nat sl.len = vs.length from Hlen.1.symm, List.take_left]
    have hb : (subslice (sint.nat sl.len) (sint.nat (sl.len + sl2.len))
        (vs.take (List.replicate (sint.nat (sl.len + sl2.len)) (zero_val V)).length ++
          (List.replicate (sint.nat (sl.len + sl2.len)) (zero_val V)).drop vs.length)).length =
        vs'.length := by
      simp only [subslice, List.length_drop, List.length_take, List.length_append,
        List.length_replicate]
      omega
    rw [ha, hb, List.take_length, List.drop_of_length_le (i := vs'.length) (by omega),
      List.append_nil]
    have hnl : nsl.len = sl.len + sl2.len := by word
    have hs : slice.slice nsl V (W64 0) (sl.len + sl2.len) = nsl := by
      rw [← hnl]; exact (slice_slice_trivial nsl).symm
    ihave H := ownSlice_combine sl.len nsl _ vs vs' (W64 0) (sl.len + sl2.len)
      ⟨by word, by word, by word, by word⟩ $$ Hnew1 Hnew2
    rw [hs]
    isplitl []
    · ipureintro; exact isPanic_intoVal _
    imodintro
    iapply HΦ
    iframe Hs2 Hnew_cap H
    iintro %vs2 _
    iexists vs
    iframe Hs Hcap
    ipureintro; left; rfl

end wps

end smd
end EtcdGrove
end Perennial
