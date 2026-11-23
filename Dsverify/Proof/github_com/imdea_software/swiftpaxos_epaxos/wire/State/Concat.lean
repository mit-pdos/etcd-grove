/-
`state.concat` (the `SCAN` result): a fresh slice holding the given values, concatenated
(internal to the state package).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.State

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.imdea_software.swiftpaxos_epaxos.kvs

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The total length of the first `n` values. -/
def lensUpTo (vs : List (GoSlice × List w8)) (n : Nat) : Nat :=
  ((vs.take n).map (fun x => x.2.length)).sum

theorem lensUpTo_succ (vs : List (GoSlice × List w8)) (n : Nat) (x : GoSlice × List w8)
    (h : vs[n]? = some x) : lensUpTo vs (n + 1) = lensUpTo vs n + x.2.length := by
  unfold lensUpTo
  rw [List.take_add_one, h]; simp

theorem flatten_take_length (vs : List (GoSlice × List w8)) (n : Nat) :
    ((vs.take n).map Prod.snd).flatten.length = lensUpTo vs n := by
  unfold lensUpTo
  rw [List.length_flatten, List.map_map]; rfl

theorem lensUpTo_le (vs : List (GoSlice × List w8)) (n : Nat) :
    lensUpTo vs n ≤ lensUpTo vs vs.length := by
  unfold lensUpTo
  rw [List.take_length]
  conv => rhs; rw [← List.take_append_drop n vs]
  rw [List.map_append, List.sum_append]
  omega

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions]
  [TH : StateTreemap GF]

omit [state.Assumptions] in
/-- `copy(dst, src)` with room for `src`: returns `len(src)`. -/
theorem wp_copy_fits (dst src : GoSlice) (vs vs' : List w8) (dq : DFrac)
    (hfit : vs'.length ≤ vs.length) :
  {{ (dst ↦* vs ∗ src ↦*{dq} vs' : IProp GF) }}
    (App (App (Val #(functions go.copy [go.GoType.SliceType go.byte])) (Val #dst)) (Val #src))
  {{ RET #(W64 (vs'.length : Int)); dst ↦* (vs' ++ vs.drop vs'.length) ∗ src ↦*{dq} vs' }} := by
  wp_start_folded as ⟨Hd, Hs⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  by_cases h0 : vs'.length = 0
  · have hz : src.len = W64 0 := by word
    wp_apply wp_slice_copy_of_len_zero (V := w8) dst src hz
    have : vs' = [] := List.eq_nil_of_length_eq_zero h0
    subst this
    iapply HΦ
    simp only [List.length_nil, List.nil_append, List.drop_zero]
    iframe
  · wp_apply wp_slice_copy (V := w8) dst vs src vs' dq $$ [$Hd $Hs] as %k ⟨%Hk, Hd, Hs⟩
    have hk : k = W64 (vs'.length : Int) := by
      have : sint.nat k = vs'.length := by rw [Hk]; omega
      word
    rw [hk, List.take_of_length_le hfit]
    iapply HΦ
    iframe

theorem state.wp_concat (sl : GoSlice) (dq : DFrac) (vs : List (GoSlice × List w8))
    (hsum : lensUpTo vs vs.length < 2 ^ 63) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.state ∗
      sl ↦*{dq} vs.map Prod.fst ∗ [∗list] x ∈ vs, x.1 ↦*□ x.2 }}
    (App (Val (@! state.concat)) (Val #sl))
  {{ (r : GoSlice), RET #r; sl ↦*{dq} vs.map Prod.fst ∗ r ↦* (vs.map Prod.snd).flatten }} := by
  wp_start as ⟨Hsl, #Hvs⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  wp_auto
  have hvl : vs.length = sint.nat sl.len := by simpa using Hlen.1
  ihave L1 : (∃ (n : w64) (sv : GoSlice),
      "i" ∷ i_ptr ↦ n ∗ "s" ∷ s_ptr ↦ sv ∗
      "totalLen" ∷ totalLen_ptr ↦ W64 (lensUpTo vs (sint.nat n) : Int) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ vs.length⌝ : IProp GF) $$ [i s totalLen]
  · iexists W64 0, _
    iframe
    ipureintro; constructor <;> word
  wp_for L1
  wp_if_destruct
  · have hi : sint.Z n < sint.Z sl.len := by simpa using Hif
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hn.1, hi⟩)]
    list_elem vs (sint.nat n) as x
    wp_apply wp_load_slice_index sl (sint.Z n) _ dq x.1 Hn.1 $$ [Hsl] with Hsl
    · iframe Hsl; ipureintro
      rw [show (sint.Z n).toNat = sint.nat n from rfl, List.getElem?_map, Hx_lookup]; rfl
    ihave #Hx := BigSepL.bigSepL_lookup Hx_lookup $$ Hvs
    ihave %Hxl := ownSlice_len _ _ _ $$ Hx
    wp_for_post
    iframe
    iexists n + W64 1, x.1
    iframe
    have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    have hs := lensUpTo_succ vs _ x Hx_lookup
    have hle := lensUpTo_le vs (sint.nat n + 1)
    rw [hn1, hs]
    isplitl
    · rw [show W64 ((lensUpTo vs (sint.nat n) : Nat) : Int) + x.1.len =
          W64 (((lensUpTo vs (sint.nat n) + x.2.length : Nat)) : Int) by word]
      iframe
    · ipureintro; constructor <;> word
  · have hnv : sint.nat n = vs.length := by word
    rw [hnv]
    have hT := hsum
    wp_apply wp_slice_make2 (V := w8) (W64 (lensUpTo vs vs.length : Int)) $$ [] as %tmp ⟨Htmp, Hcap⟩
    · ipureintro; word
    rename_i off_ptr
    irename : (off_ptr ↦ zero_val w64 : IProp GF) => off
    have hTn : sint.nat (W64 (lensUpTo vs vs.length : Int)) = lensUpTo vs vs.length := by word
    rw [hTn]
    ihave %Htl := ownSlice_len _ _ _ $$ Htmp
    ihave %Htwf := ownSlice_wf _ _ _ $$ Htmp
    rw [List.length_replicate] at Htl
    ihave L2 : (∃ (n : w64) (sv : GoSlice),
        "i" ∷ i_ptr ↦ n ∗ "s" ∷ s_ptr ↦ sv ∗
        "off" ∷ off_ptr ↦ W64 (lensUpTo vs (sint.nat n) : Int) ∗
        "Htmp" ∷ tmp ↦* (((vs.take (sint.nat n)).map Prod.snd).flatten ++
          List.replicate (lensUpTo vs vs.length - lensUpTo vs (sint.nat n)) (W8 0)) ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ vs.length⌝ : IProp GF) $$ [i s off Htmp]
    · iexists W64 0, _
      iframe
      ipureintro; constructor <;> word
    wp_for L2
    wp_if_destruct
    · have hi : sint.Z n < sint.Z sl.len := by
        by_cases h : sint.Z n < sint.Z sl.len
        · exact h
        · exact absurd Hif h
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hn.1, hi⟩)]
      list_elem vs (sint.nat n) as x
      wp_apply wp_load_slice_index sl (sint.Z n) _ dq x.1 Hn.1 $$ [Hsl] with Hsl
      · iframe Hsl; ipureintro
        rw [show (sint.Z n).toNat = sint.nat n from rfl, List.getElem?_map, Hx_lookup]; rfl
      ihave #Hx := BigSepL.bigSepL_lookup Hx_lookup $$ Hvs
      ihave %Hxl := ownSlice_len _ _ _ $$ Hx
      have hs := lensUpTo_succ vs _ x Hx_lookup
      have hle := lensUpTo_le vs (sint.nat n + 1)
      generalize hL : lensUpTo vs (sint.nat n) = L at *
      generalize hT : lensUpTo vs vs.length = T at *
      have hLz : sint.Z (W64 (L : Int)) = L := by word
      have hLn : sint.nat (W64 (L : Int)) = L := by word
      have htl : sint.Z tmp.len = T := by word
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega, Htwf.2⟩)]
      have hfl := flatten_take_length vs (sint.nat n)
      rw [hL] at hfl
      icases (ownSlice_split_all (W64 (L : Int)) tmp _ _ ⟨by omega, by omega⟩).1 $$ Htmp
        with ⟨H0, H1⟩
      rw [hLn, List.take_left' hfl, List.drop_left' hfl]
      wp_auto
      wp_apply wp_copy_fits _ _ _ x.2 DFrac.discard (by rw [List.length_replicate]; omega)
        $$ [$H1 $Hx] as ⟨H1, -⟩
      rw [List.drop_replicate]
      ihave Htmp := ownSlice_combine (W64 (L : Int)) tmp _ _ _ (W64 0) tmp.len
        ⟨by rw [hLn, hfl]; rfl, by decide, by rw [hLz]; word, by omega⟩ $$ H0 H1
      ihave Htmp := (ownSlice_trivial_slice tmp _ _).2 $$ Htmp
      wp_for_post
      iframe
      iexists n + W64 1, x.1
      iframe
      have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
      rw [hn1, hs, List.take_add_one, Hx_lookup]
      simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil,
        List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]
      rw [Nat.sub_add_eq]
      isplitl [off]
      · rw [show W64 (L : Int) + W64 (x.2.length : Int) = W64 ((L + x.2.length : Nat) : Int) by
          word]
        iframe
      · iframe; ipureintro; constructor <;> word
    · have hnv2 : sint.nat n = vs.length := by word
      rw [hnv2, List.take_length, Nat.sub_self, List.replicate_zero, List.append_nil]
      iapply HΦ
      iframe

end heap
end Perennial.github_com.imdea_software.swiftpaxos_epaxos
