/-
The proof of `Spec/encoding/base64/NewEncoding.lean`. Lean-first.
-/
module

public import Spec.encoding.base64.NewEncoding
public import Proof.encoding.base64.Lemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.encoding.base64.Assumptions]

theorem base64.NewEncoding.wp_proof :
    base64.NewEncoding.spec (GF := GF) (hG := hG) := by
  intro s hlen hnd h10 h13
  wp_start
  try wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hl
  try wp_auto
  rw [hlen]
  simp only [show W64 ((64 : Nat) : Int) = W64 64 from rfl, decide_true, Bool.not_true,
    _root_.Perennial.encoding.base64.StdPadding]
  try wp_auto
  icases base64.enc_open _ _ _ $$ «$r0» with ⟨%Hnn, Hf⟩
  icases Hf with ⟨Henc, Hdm, Hpad, Hstrict⟩
  wp_apply (wp_string_to_bytes s) as %sl ⟨Hsl, -⟩
  try wp_auto
  ihave Hdst := base64.array_slice0 _ 64 _ (by decide) $$ Henc
  wp_apply (wp_slice_copy _ _ sl s (DFrac.own 1)) $$ [Hdst Hsl] as %n ⟨%hn1, Hdst, -⟩
  · iframe
  ihave Henc := base64.slice0_array _ 64 _ ⟨by decide, by decide⟩ $$ Hdst
  have hz1 : (zero_val _root_.Perennial.encoding.base64.Encoding).encode'.arr = List.replicate 64 0 := rfl
  have hz2 : (zero_val _root_.Perennial.encoding.base64.Encoding).decodeMap'.arr =
    List.replicate 256 0 := rfl
  have hdmi : _root_.Perennial.encoding.base64.decodeMapInitialize =
    #(List.replicate 256 (W8 255) : GoString) := by set_option maxRecDepth 100000 in rfl
  simp only [hz1, hz2, hdmi, hlen, List.length_replicate, List.take_length, List.drop_of_length_le (Nat.le_refl _)]
  try wp_auto
  wp_apply (wp_string_to_bytes (List.replicate 256 (W8 255))) as %sl2 ⟨Hsl2, -⟩
  try wp_auto
  ihave Hdst := base64.array_slice0 _ 256 _ (by decide) $$ Hdm
  wp_apply (wp_slice_copy _ _ sl2 _ (DFrac.own 1)) $$ [Hdst Hsl2] as %n2 ⟨%hn2, Hdst, -⟩
  · iframe
  ihave Hdm := base64.slice0_array _ 256 _ ⟨by decide, by decide⟩ $$ Hdst
  simp only [hz2, List.length_replicate, List.take_replicate, List.drop_replicate, Nat.min_self,
    Nat.sub_self, List.replicate_zero, List.append_nil]
  try wp_auto
  ihave HI : (∃ (i : Nat), "i" ∷ i_ptr ↦ W64 (i : Int) ∗
      "Hdm" ∷ structFieldRef _root_.Perennial.encoding.base64.Encoding go!"decodeMap" «$r0_ptr» ↦
        (array.mk 256 (base64.dmAfter s i) : GoArray w8 256) ∗
      "%Hi" ∷ ⌜i ≤ 64⌝ : IProp GF) $$ [i Hdm]
  · iexists 0
    simp only [base64.dmAfter, List.range_zero, List.foldl_nil]
    isplitl [i]
    · iexact i
    isplitl [Hdm]
    · iexact Hdm
    ipureintro; omega
  wp_for HI
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %_
  rw [hlen]
  try wp_auto
  wp_if_destruct
  · have hi64 : i < 64 := by
      have h := go.intoVal_inj Hif; simp only [decide_eq_true_eq] at h
      revert h; word
    have hi0 : 0 ≤ sint.Z (W64 (i : Int)) := by word
    have hsn : sint.nat (W64 (i : Int)) = i := by word
    have hsi : s[i]? = some (s[i]'(by omega)) := List.getElem?_eq_getElem _
    have hm : (s[i]'(by omega)) ∈ s := List.getElem_mem _
    have hn10 : (s[i]'(by omega)) ≠ W8 10 := fun h => h10 (by rw [show (10 : w8) = W8 10 from rfl, ← h]; exact hm)
    have hn13 : (s[i]'(by omega)) ≠ W8 13 := fun h => h13 (by rw [show (13 : w8) = W8 13 from rfl, ← h]; exact hm)
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true hi0), hsn, hsi]
    try wp_auto
    simp only [hn10, decide_false]
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true hi0), hsn, hsi]
    try wp_auto
    simp only [hn13, decide_false]
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true hi0), hsn, hsi]
    try wp_auto
    have hb : 0 ≤ sint.Z (W64 (uint.Z (s[i]'(by omega)))) ∧ sint.Z (W64 (uint.Z (s[i]'(by omega)))) < 256 := by
      word
    have hbz : (sint.Z (W64 (uint.Z (s[i]'(by omega))))).toNat = (s[i]'(by omega)).toNat := by word
    have hfree : (s[i]'(by omega)) ∉ s.take i := by
      intro h
      obtain ⟨j, hj, hji⟩ := List.mem_iff_getElem.1 h
      simp only [List.length_take] at hj
      rw [List.getElem_take] at hji
      exact List.pairwise_iff_getElem.1 hnd j i (by omega) (by omega) (by omega) hji
    rw [ite_eq_left_of_eq_true _ _ (eq_true hb)]
    wp_apply (base64.wp_load_arr _ 256 _ (DFrac.own 1) _ hb) $$ Hdm as Hdm
    simp only [hbz, base64.dmAfter_free s _ i (by omega) hfree, _root_.Perennial.encoding.base64.invalidIndex]
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true hi0), hsn, hsi]
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true hb)]
    wp_apply (base64.wp_store_arr _ 256 _ _ _ hb) $$ Hdm as Hdm
    try wp_auto
    wp_for_post
    iframe
    iexists (i + 1)
    have hgd : s.getD i 0 = s[i]'(by omega) := by
      simp [List.getD, List.getElem?_eq_getElem (show i < s.length by omega)]
    have hw : W8 (sint.Z (W64 (i : Int))) = W8 ((i : Nat) : Int) := by word
    rw [show W64 (i : Int) + W64 1 = W64 ((i + 1 : Nat) : Int) by word, base64.dmAfter_succ, hgd, hbz, hw]
    iframe
    ipureintro; omega
  · have hP : ¬ (sint.Z (W64 (i : Int)) < sint.Z (W64 ((64 : Nat) : Int))) := fun h => Hif (by rw [decide_eq_true h])
    have hi64 : i = 64 := by revert hP; word
    rw [show decide (sint.Z (W64 (i : Int)) < sint.Z (W64 ((64 : Nat) : Int))) = false from decide_eq_false hP]
    simp only [Bool.false_eq_true, ↓reduceIte]
    subst hi64
    try wp_auto
    iapply HΦ
    iexists (_root_.Perennial.encoding.base64.Encoding.mk (array.mk 64 s) (array.mk 256 (base64.dmAfter s 64))
      (W32 61) (zero_val _root_.Perennial.encoding.base64.Encoding).strict')
    isplitl [Henc Hdm Hpad Hstrict]
    · iapply base64.enc_close _ _ _ Hnn
      unfold base64.encFields
      rw [List.take_of_length_le (by omega)] 
      iframe
    ipureintro; exact ⟨rfl, rfl⟩

end proof

end EtcdGrove
end Perennial
