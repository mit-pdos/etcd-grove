/-
The proof of `Spec/hash/crc32/slicingMakeTable.lean`: table `0` by `simplePopulateTable`, then entry by
entry the other seven (`slicingEntry_succ`).
-/
module

public import Spec.hash.crc32.slicingMakeTable
public import Spec.hash.crc32.simplePopulateTable
public import Proof.hash.crc32.Slicing
public import Proof.hash.crc32.TableLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [hash.crc32.Assumptions]

namespace hash.crc32

/-- The table after the rounds `< i` of the outer loop and, in round `i`, the tables `< j` of the
inner loop (table `0` is `simplePopulateTable`'s). -/
def smtAt (poly : w32) (i j : Nat) : Nat → Nat → w32 := fun j' k =>
  if j' = 0 ∨ k < i ∨ (k = i ∧ j' < j) then _root_.Perennial.hash.crc32.slicingEntry poly j' k else 0#32

theorem tabOf_congr (f g : Nat → Nat → w32) (h : ∀ j < 8, ∀ k < 256, f j k = g j k) :
    tabOf f = tabOf g := by
  unfold tabOf
  congr 1
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  congr 1
  apply List.map_congr_left
  intro k hk
  rw [List.mem_range] at hk
  exact h j hj k hk

theorem smtAt_init (poly : w32) :
    tabOf (fun j' => if j' = 0 then _root_.Perennial.hash.crc32.crcTableEntry poly else (fun _ _ => 0#32) j') =
      tabOf (smtAt poly 0 1) := by
  apply tabOf_congr
  intro j _ k _
  unfold smtAt
  by_cases h : j = 0
  · subst h; simp only [↓reduceIte, true_or]; rfl
  · simp [h]

theorem smtAt_store (poly : w32) (i j : Nat) :
    (fun j' k' => if j' = j ∧ k' = i then _root_.Perennial.hash.crc32.slicingEntry poly j i
      else smtAt poly i j j' k') = smtAt poly i (j + 1) := by
  funext j' k'
  unfold smtAt
  by_cases h : j' = j ∧ k' = i
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [if_neg h]
    by_cases h1 : j' = 0 ∨ k' < i ∨ k' = i ∧ j' < j <;>
      by_cases h2 : j' = 0 ∨ k' < i ∨ k' = i ∧ j' < j + 1 <;>
      simp only [h1, h2, ↓reduceIte] <;> (exfalso; omega)

theorem smtAt_next (poly : w32) (i : Nat) : tabOf (smtAt poly i 8) = tabOf (smtAt poly (i + 1) 1) := by
  apply tabOf_congr
  intro j hj k _
  unfold smtAt
  by_cases h1 : j = 0 ∨ k < i ∨ k = i ∧ j < 8 <;>
    by_cases h2 : j = 0 ∨ k < i + 1 ∨ k = i + 1 ∧ j < 1 <;>
    simp only [h1, h2, ↓reduceIte] <;> (exfalso; omega)

theorem smtAt_done (poly : w32) :
    tabOf (smtAt poly 256 1) = tabOf (_root_.Perennial.hash.crc32.slicingEntry poly) := by
  apply tabOf_congr
  intro j _ k hk
  simp [smtAt, hk]

theorem and255_lt (c : w32) : (c &&& 0xff#32).toNat < 256 := by
  rw [BitVec.toNat_and]
  have := @Nat.and_le_right c.toNat (0xff#32).toNat
  have h255 : (0xff#32).toNat = 255 := rfl
  omega

theorem and255_idx (c : w32) :
    sint.Z (W64 (uint.Z (c &&& W32 255))) = (((c &&& 0xff#32).toNat : Nat) : Int) := by
  have := and255_lt c
  have e : W32 255 = 0xff#32 := rfl
  rw [e]
  simp only [uint.Z, sint.Z]; word

end hash.crc32

theorem hash.crc32.slicingMakeTable.wp_proof
    (hpop : hash.crc32.simplePopulateTable.spec (GF := GF) (hG := hG)) :
    hash.crc32.slicingMakeTable.spec (GF := GF) (hG := hG) := by
  intro poly
  wp_start as -
  wp_apply IntoValTyped.wp_alloc (t := go.GoType.PointerType hash.crc32.slicing8Table.ty) (zero_val Loc) as %r Hr
  try wp_auto
  rw [show sint.Z (W64 0) = ((0 : Nat) : Int) from rfl, hash.crc32.tabOf_zero]
  icases hash.crc32.tabOf_row_acc _ _ _ 0 (by omega) $$ «$r0» with ⟨Hr0, Hb⟩
  wp_apply hpop $$ [Hr0] as Hr0
  · iexact Hr0
  unfold _root_.Perennial.hash.crc32.crcTableOf
  ihave Ht := Hb $$ %(_root_.Perennial.hash.crc32.crcTableEntry poly) Hr0
  rw [hash.crc32.smtAt_init]
  try wp_auto
  ihave HI : iprop(∃ (i : Nat), "i" ∷ i_ptr ↦ W64 (i : Int) ∗
      "Ht" ∷ «$r0_ptr» ↦ hash.crc32.tabOf (hash.crc32.smtAt poly i 1) ∗ "%Hi" ∷ ⌜i ≤ 256⌝) $$ [i Ht]
  · iexists 0
    iframe
    ipureintro; omega
  wp_for HI
  wp_if_destruct
  · have hi256 : i < 256 := by revert Hif; word
    have hzi : sint.Z (W64 (i : Int)) = (i : Int) := by word
    have hz0 : sint.Z (W64 0) = ((0 : Nat) : Int) := rfl
    try wp_auto
    rw [hzi, hz0, ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩)]
    wp_apply hash.crc32.wp_load_tabOf _ _ _ 0 i (by omega) hi256 $$ [Ht] as Ht
    · iexact Ht
    have he0 : hash.crc32.smtAt poly i 1 0 i = _root_.Perennial.hash.crc32.slicingEntry poly 0 i := by
      simp [hash.crc32.smtAt]
    rw [he0]
    try wp_auto
    ihave HJ : iprop(∃ (j : Nat), "j" ∷ j_ptr ↦ W64 (j : Int) ∗
        "crc" ∷ crc_ptr ↦ _root_.Perennial.hash.crc32.slicingEntry poly (j - 1) i ∗
        "Ht" ∷ «$r0_ptr» ↦ hash.crc32.tabOf (hash.crc32.smtAt poly i j) ∗
        "%Hj" ∷ ⌜1 ≤ j ∧ j ≤ 8⌝) $$ [j crc Ht]
    · iexists 1
      iframe
      ipureintro; omega
    wp_for HJ
    wp_if_destruct
    · have hj8 : j < 8 := by revert Hif; word
      try wp_auto
      generalize hc : _root_.Perennial.hash.crc32.slicingEntry poly (j - 1) i = c
      have hk := hash.crc32.and255_idx c
      have hk256 := hash.crc32.and255_lt c
      rw [hk, hz0, ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩)]
      wp_apply hash.crc32.wp_load_tabOf _ _ _ 0 _ (by omega) hk256 $$ [Ht] as Ht
      · iexact Ht
      have he : hash.crc32.smtAt poly i j 0 (c &&& 0xff#32).toNat ^^^ c >>> W64 8 =
          _root_.Perennial.hash.crc32.slicingEntry poly j i := by
        have hj1 : j = (j - 1) + 1 := by omega
        rw [hj1, _root_.Perennial.hash.crc32.slicingEntry_succ, hc]
        simp [hash.crc32.smtAt, _root_.Perennial.hash.crc32.slicingEntry_zero]
      rw [he]
      try wp_auto
      have hzj : sint.Z (W64 (j : Int)) = (j : Int) := by word
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩)]
      try wp_auto
      rw [hzi, ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩), hzj]
      wp_apply hash.crc32.wp_store_tabOf _ _ j i (by omega) hi256 $$ [Ht] as Ht
      · iexact Ht
      rw [hash.crc32.smtAt_store]
      wp_for_post
      iframe
      iexists (j + 1)
      rw [show W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) by word, Nat.add_sub_cancel]
      iframe
      ipureintro; omega
    · have hj : j = 8 := by revert Hif; word
      subst hj
      try wp_auto
      wp_for_post
      iframe
      iexists (i + 1)
      rw [show W64 (i : Int) + W64 1 = W64 ((i + 1 : Nat) : Int) by word, ← hash.crc32.smtAt_next]
      iframe
      ipureintro; omega
  · have hi : i = 256 := by revert Hif; word
    subst hi
    try wp_auto
    rw [hash.crc32.smtAt_done, ← hash.crc32.slicingTableArr_tabOf]
    iapply HΦ
    iexact Ht

end proof

end EtcdGrove
end Perennial
