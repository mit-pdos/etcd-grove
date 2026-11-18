/-
The proof of `Spec/io/fs/FileMode__String.lean`: two range loops over constant strings (13 and 9
runes), each writing at most one byte per rune into a `[32]byte` at index `w`, `w` at most the
runes seen so far (plus one for the hyphen), so every index is below 32; then `string(buf[:w])`.
-/
module

public import Spec.io.fs.FileMode__String

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

/-- A range loop over `s` runs at most `fuel` iterations. -/
private theorem runesFrom_length_le (s : GoString) : ∀ (fuel k : Nat), (go.runesFrom s fuel k).length ≤ fuel
  | 0, _ => by simp [go.runesFrom]
  | fuel + 1, k => by
    simp only [go.runesFrom]
    split
    · simp only [List.length_cons]; have := runesFrom_length_le s fuel (go.decodeRune s k).2; omega
    · simp

/-- A range loop over `s` runs at most `len(s)` iterations. -/
private theorem runes_length_le (s : GoString) : (go.runes s).length ≤ s.length :=
  runesFrom_length_le s s.length 0

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [io.fs.Assumptions]

/-- The `n`-th byte of the buffer, and the buffer back with it replaced. -/
private theorem buf_acc (p : Loc) (a : GoArray w8 32) (n : Nat) (hl : a.arr.length = 32) (hn : n < 32) :
    (p ↦ a : IProp GF) ⊢ arrayIndexRef w8 (n : Int) p ↦ a.arr[n]'(by omega) ∗
      (∀ v : w8, arrayIndexRef w8 (n : Int) p ↦ v -∗
        p ↦ (array.mk 32 (a.arr.set n v) : GoArray w8 32)) := by
  have h := array_acc (GF := GF) p (n : Int) (DFrac.own 1) 32 a (a.arr[n]'(by omega)) (by omega)
    (by simp)
  simpa using h

theorem fs.FileMode.String.wp_proof : fs.FileMode.String.spec (GF := GF) (hG := hG) := by
  intro mode
  wp_start
  wp_auto
  have hj1 := runes_length_le [100#8, 97#8, 108#8, 84#8, 76#8, 68#8, 112#8, 83#8, 117#8, 103#8, 99#8, 116#8, 63#8]
  simp only [List.length_cons, List.length_nil] at hj1
  wp_apply (wp_string_for_range _ _ (fun j => iprop(∃ (a : GoArray w8 32) (n : Nat) (cv : w32) (iv : w64),
      buf_ptr ↦ a ∗ w_ptr ↦ W64 (n : Int) ∗ c_ptr ↦ cv ∗ i_ptr ↦ iv ∗ m_ptr ↦ mode ∗
      ⌜n ≤ j ∧ a.arr.length = 32⌝))) $$ [buf w c i m]
  · iexists zero_val (GoArray w8 32), 0, zero_val w32, zero_val w64
    iframe
    ipureintro; exact ⟨Nat.zero_le _, rfl⟩
  · imodintro
    iintro %j %k %r %hk ⟨%a, %n, %cv, %iv, Hb, Hw, Hc, Hi, Hm, %hn⟩
    have hjl : j < 13 := by
      have := (List.getElem?_eq_some_iff.1 hk).1
      omega
    wp_auto
    wp_if_destruct
    · iapply forRangePostcondition_do
      iexists a, n, r, W64 (k : Int)
      iframe
      ipureintro; exact ⟨by omega, hn.2⟩
    · have hsn : sint.Z (W64 (n : Int)) = (n : Int) := by word
      rw [hsn, ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
      icases buf_acc buf_ptr a n hn.2 (by omega) $$ Hb with ⟨Hel, Hb⟩
      wp_auto
      ihave Hb := Hb $$ Hel
      iapply forRangePostcondition_do
      have hw : W64 (n : Int) + W64 1 = W64 ((n + 1 : Nat) : Int) := by word
      rw [hw]
      iexists _, n + 1, r, W64 (k : Int)
      iframe
      ipureintro; exact ⟨by omega, by simp [hn.2]⟩
  iintro ⟨%a1, %n1, %cv1, %iv1, Hb, Hw, Hc, Hi, Hm, %hn1⟩
  wp_auto
  wp_join iprop(∃ (a1 : GoArray w8 32) (n1 : Nat), buf_ptr ↦ a1 ∗ w_ptr ↦ W64 (n1 : Int) ∗
      ⌜n1 ≤ 13 ∧ a1.arr.length = 32⌝) with [Hb Hw]
  · have hn13 : n1 ≤ 13 := by omega
    have hn0 : n1 = 0 := by
      have h := congrArg (fun x : w64 => sint.Z x) Hif
      have : sint.Z (W64 (n1 : Int)) = (n1 : Int) := by word
      rw [this] at h
      simpa using h
    have hsn : sint.Z (W64 (n1 : Int)) = (n1 : Int) := by word
    rw [hsn, ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
    icases buf_acc buf_ptr a1 n1 hn1.2 (by omega) $$ Hb with ⟨Hel, Hb⟩
    wp_auto
    ihave Hb := Hb $$ Hel
    wp_join_done
    iexists _, n1 + 1
    rw [show W64 (n1 : Int) + W64 1 = W64 ((n1 + 1 : Nat) : Int) by word]
    iframe
    ipureintro; exact ⟨by omega, by simp [hn1.2]⟩
  · iexists a1, n1
    iframe
    ipureintro; exact ⟨by omega, hn1.2⟩
  iintro ⟨%a2, %n2, Hb, Hw, %hn2⟩
  wp_auto
  have hj2 := runes_length_le [114#8, 119#8, 120#8, 114#8, 119#8, 120#8, 114#8, 119#8, 120#8]
  simp only [List.length_cons, List.length_nil] at hj2
  wp_apply (wp_string_for_range _ _ (fun j => iprop(∃ (a2 : GoArray w8 32) (n2 : Nat) (cv2 : w32) (iv2 : w64),
      buf_ptr ↦ a2 ∗ w_ptr ↦ W64 (n2 : Int) ∗ c_ptr ↦ cv2 ∗ i_ptr ↦ iv2 ∗ m_ptr ↦ mode ∗
      ⌜n2 ≤ 13 + j ∧ a2.arr.length = 32⌝))) $$ [Hb Hw c i Hm]
  · iexists a2, n2, zero_val w32, zero_val w64
    iframe
    ipureintro; exact ⟨by omega, hn2.2⟩
  · imodintro
    iintro %j %k %r %hk ⟨%a, %n, %cv, %iv, Hb, Hw, Hc, Hi, Hm, %hn⟩
    have hjl : j < 9 := by
      have := (List.getElem?_eq_some_iff.1 hk).1
      omega
    have hsn : sint.Z (W64 (n : Int)) = (n : Int) := by word
    wp_auto
    wp_join iprop(∃ (a : GoArray w8 32), buf_ptr ↦ a ∗ w_ptr ↦ W64 (n : Int) ∗ c_ptr ↦ r ∗
      ⌜a.arr.length = 32⌝) with [Hb Hw Hc]
    · rw [hsn, ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
      icases buf_acc buf_ptr a n hn.2 (by omega) $$ Hb with ⟨Hel, Hb⟩
      wp_auto
      ihave Hb := Hb $$ Hel
      wp_join_done
      iexists _
      iframe
      ipureintro; simp [hn.2]
    · rw [hsn, ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
      icases buf_acc buf_ptr a n hn.2 (by omega) $$ Hb with ⟨Hel, Hb⟩
      wp_auto
      ihave Hb := Hb $$ Hel
      wp_join_done
      iexists _
      iframe
      ipureintro; simp [hn.2]
    iintro ⟨%a', Hb, Hw, Hc, %ha'⟩
    wp_auto
    iapply forRangePostcondition_do
    iexists a', n + 1, r, W64 (k : Int)
    rw [show W64 (n : Int) + W64 1 = W64 ((n + 1 : Nat) : Int) by word]
    iframe
    ipureintro; exact ⟨by omega, ha'⟩
  iintro ⟨%a4, %n4, %cv4, %iv4, Hb, Hw, Hc, Hi, Hm, %hn4⟩
  wp_auto
  have hsn4 : sint.Z (W64 (n4 : Int)) = (n4 : Int) := by word
  have hc : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 (n4 : Int)) ∧
      sint.Z (W64 (n4 : Int)) ≤ 32 := by
    have h0 : sint.Z (W64 0) = 0 := by decide
    rw [hsn4, h0]; omega
  rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
  have hl4 : a4.arr.length < 2 ^ 63 := by omega
  have hk4 : 0 ≤ sint.Z (W64 (n4 : Int)) ∧ sint.Z (W64 (n4 : Int)) ≤ sint.Z (W64 32) := by
    have h32 : sint.Z (W64 32) = 32 := by decide
    rw [hsn4, h32]; omega
  ihave Hsl := slice_array (V := w8) buf_ptr 32 a4 hl4 $$ Hb
  icases (ownSlice_split_all (W64 (n4 : Int)) (slice.mk buf_ptr (W64 32) (W64 32)) _ _ hk4).1 $$ Hsl
    with ⟨Hsl, -⟩
  unfold slice.slice sliceIndexRef
  wp_apply wp_bytes_to_string _ _ _ $$ Hsl as Hsl
  iapply HΦ
  ipureintro; trivial
