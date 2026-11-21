/-
The proof of `sort.pdqsort` for any `Less` (`Spec/sort/pdqsortAnyLess.lean`): Perennial's proof (`Perennial/Proof/sort/pdqsort.lean`: Löb induction for the recursive calls, the outer loop's invariant, the joins after each `if`) without the order: the invariant keeps only `0 ≤ a ≤ b ≤ len` and a permutation of the list.
-/
module

public import Spec.sort.pdqsortAnyLess
public import Spec.sort.insertionSortAnyLess
public import Spec.sort.heapSortAnyLess
public import Spec.sort.breakPatternsAnyLess
public import Spec.sort.choosePivotAnyLess
public import Spec.sort.reverseRangeAnyLess
public import Spec.sort.partialInsertionSortAnyLess
public import Spec.sort.partitionEqualAnyLess
public import Spec.sort.partitionAnyLess
public import Proof.sort.AnyLessBasics

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open sortAny

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.sort.Assumptions]

theorem sort.pdqsort.wp_proofAnyLess
    (wp_insertionSort : EtcdGrove.sort.insertionSort.anyLessSpec (GF := GF) (hG := hG))
    (wp_heapSort : EtcdGrove.sort.heapSort.anyLessSpec (GF := GF) (hG := hG))
    (wp_breakPatterns : EtcdGrove.sort.breakPatterns.anyLessSpec (GF := GF) (hG := hG))
    (wp_choosePivot : EtcdGrove.sort.choosePivot.anyLessSpec (GF := GF) (hG := hG))
    (wp_reverseRange : EtcdGrove.sort.reverseRange.anyLessSpec (GF := GF) (hG := hG))
    (wp_partialInsertionSort :
      EtcdGrove.sort.partialInsertionSort.anyLessSpec (GF := GF) (hG := hG))
    (wp_partitionEqual : EtcdGrove.sort.partitionEqual.anyLessSpec (GF := GF) (hG := hG))
    (wp_partition : EtcdGrove.sort.partition.anyLessSpec (GF := GF) (hG := hG)) :
    EtcdGrove.sort.pdqsort.anyLessSpec (GF := GF) (hG := hG) := fun E x R l a b limit => by
  iloeb as IH generalizing %l %a %b %limit
  irevert IH
  iapply anyHide_intro
  iintro #IH
  wp_start as ⟨#Hs, Hl, %Hab_bound⟩
  wp_auto
  -- the outer loop's invariant
  ihave HI : (∃ (a_val b_val limit : w64) (bl1 bl2 : Bool) (L : List E),
      "a" ∷ a_ptr ↦ a_val ∗
      "b" ∷ b_ptr ↦ b_val ∗
      "limit" ∷ limit_ptr ↦ limit ∗
      "wasPartitioned" ∷ wasPartitioned_ptr ↦ bl1 ∗
      "wasBalanced" ∷ wasBalanced_ptr ↦ bl2 ∗
      "Hl" ∷ R L ∗
      "%ab_range" ∷ ⌜0 ≤ sint.Z a_val ∧ sint.Z a_val ≤ sint.Z b_val ∧
        sint.Z b_val ≤ l.length⌝ ∗
      "%HPerm1" ∷ ⌜l.Perm L⌝ : IProp GF)
      $$ [a b limit Hl wasPartitioned wasBalanced]
  · iexists a, b, limit, true, true, l
    iframe
    ipureintro
    exact ⟨⟨by omega, by omega, by omega⟩, List.Perm.refl _⟩
  wp_for HI
  have Hlen1 := HPerm1.length_eq
  wp_if_destruct
  · -- falls to insertionSort
    wp_apply wp_insertionSort E x R L a_val b_val $$ [Hl] with %L' ⟨Hl, %HP'⟩
    · iframe Hl; iframe #; ipureintro; word
    wp_for_post
    iapply HΦ
    iframe Hl
    ipureintro
    exact HPerm1.trans HP'
  wp_if_destruct
  · -- falls to heapSort
    wp_apply wp_heapSort E x R L a_val b_val $$ [Hl] with %L' ⟨Hl, %HP'⟩
    · iframe Hl; iframe #; ipureintro; word
    wp_for_post
    iapply HΦ
    iframe Hl
    ipureintro
    exact HPerm1.trans HP'
  -- pattern breaking
  wp_bind (if: _ then _ else _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ ∃ (limit : w64) (L : List E),
      "a" ∷ a_ptr ↦ a_val ∗
      "b" ∷ b_ptr ↦ b_val ∗
      "data" ∷ data_ptr ↦ GoInterface.ok x ∗
      "limit" ∷ limit_ptr ↦ limit ∗
      "Hl" ∷ R L ∗
      "%HPerm2" ∷ ⌜l.Perm L⌝))) $$ [a b data limit Hl]
  · cases bl2
    · simp only [Bool.not_false]
      wp_auto
      wp_apply wp_breakPatterns E x R L a_val b_val $$ [Hl] with %L2 ⟨Hl, %HP2⟩
      · iframe Hl; iframe #; ipureintro; word
      isplitr
      · ipureintro; first | rfl | trivial
      iexists _, L2
      iframe
      ipureintro
      exact HPerm1.trans HP2
    · simp only [Bool.not_true]
      wp_auto
      isplitr
      · ipureintro; first | rfl | trivial
      iexists _, L
      iframe
      ipureintro
      exact HPerm1
  iintro %v ⟨%Hv, %limit1, %L2, Hpost⟩
  subst Hv
  iNamed Hpost
  clear HPerm1 Hlen1
  have Hlen2 := HPerm2.length_eq
  wp_auto
  wp_apply wp_choosePivot E x R L2 a_val b_val $$ [Hl] with %r %hint ⟨Hl, %Hrbound⟩
  · iframe Hl; iframe #; ipureintro; word
  -- reverse a decreasing range
  wp_bind (if: _ then _ else _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
      ∃ (L : List E) (hint : _root_.Perennial.sort.sortedHint) (r : w64),
      "a" ∷ a_ptr ↦ a_val ∗
      "b" ∷ b_ptr ↦ b_val ∗
      "data" ∷ data_ptr ↦ GoInterface.ok x ∗
      "hint" ∷ hint_ptr ↦ hint ∗
      "pivot" ∷ pivot_ptr ↦ r ∗
      "Hl" ∷ R L ∗
      "%HPerm3" ∷ ⌜l.Perm L⌝ ∗
      "%rrange" ∷ ⌜sint.Z a_val ≤ sint.Z r ∧ sint.Z r < sint.Z b_val⌝)))
      $$ [a b data hint pivot Hl]
  · try simp only [_root_.Perennial.sort.decreasingHint, _root_.Perennial.sort.increasingHint]
    wp_pures
    wp_if_destruct
    · wp_apply wp_reverseRange E x R L2 a_val b_val $$ [Hl] with %L3 ⟨Hl, %HP3⟩
      · iframe Hl; iframe #; ipureintro; word
      isplitr
      · ipureintro; first | rfl | trivial
      iexists L3, _, _
      iframe
      ipureintro
      exact ⟨HPerm2.trans HP3, by word⟩
    · isplitr
      · ipureintro; first | rfl | trivial
      iexists L2, _, _
      iframe
      ipureintro
      exact ⟨HPerm2, Hrbound⟩
  iintro %v ⟨%Hv, %L3, %hint3, %r3, Hpost⟩
  subst Hv
  iNamed Hpost
  clear HPerm2 Hlen2 Hrbound
  have Hlen3 := HPerm3.length_eq
  wp_auto
  -- partial insertion sort if the slice looks sorted
  wp_bind (if: _ then _ else _)
  iapply (wp_wand (Φ := fun v => iprop(∃ (L4 : List E),
      "a" ∷ a_ptr ↦ a_val ∗
      "b" ∷ b_ptr ↦ b_val ∗
      "data" ∷ data_ptr ↦ GoInterface.ok x ∗
      "hint" ∷ hint_ptr ↦ hint3 ∗
      "pivot" ∷ pivot_ptr ↦ r3 ∗
      "wasPartitioned" ∷ wasPartitioned_ptr ↦ bl1 ∗
      "wasBalanced" ∷ wasBalanced_ptr ↦ bl2 ∗
      "Hl" ∷ R L4 ∗
      "%HPerm4" ∷ ⌜l.Perm L4⌝ ∗
      "%Hpost4" ∷ ⌜v = returnVal #() ∨ v = executeVal⌝)))
      $$ [a b data hint pivot Hl wasPartitioned wasBalanced]
  · try simp only [_root_.Perennial.sort.increasingHint]
    cases bl2
    · wp_auto
      iexists L3; iframe; ipureintro
      refine ⟨HPerm3, ?_⟩
      first | exact Or.inr rfl | trivial | simp
    cases bl1
    · wp_auto
      iexists L3; iframe; ipureintro
      refine ⟨HPerm3, ?_⟩
      first | exact Or.inr rfl | trivial | simp
    wp_auto
    wp_if_destruct
    · wp_apply wp_partialInsertionSort E x R L3 a_val b_val $$ [Hl]
        with %L4 %bl ⟨Hl, %HP4⟩
      · iframe Hl; iframe #; ipureintro; word
      cases bl
      · wp_auto
        iexists L4; iframe; ipureintro
        refine ⟨HPerm3.trans HP4, ?_⟩
        first | exact Or.inr rfl | trivial | simp
      · wp_auto
        iexists L4; iframe; ipureintro
        refine ⟨HPerm3.trans HP4, ?_⟩
        first | exact Or.inl rfl | trivial | simp
    · iexists L3; iframe; ipureintro
      refine ⟨HPerm3, ?_⟩
      first | exact Or.inr rfl | trivial | simp
  iintro %v ⟨%L4, Hpost⟩
  iNamed Hpost
  rcases Hpost4 with Hv | Hv
  · subst Hv
    wp_auto
    wp_for_post
    iapply HΦ
    iframe Hl
    ipureintro
    exact HPerm4
  subst Hv
  have Hlen4 := HPerm4.length_eq
  clear HPerm3 Hlen3
  wp_auto
  -- the pivot is not greater than its predecessor: partition equal elements
  wp_bind (if: _ then _ else _)
  iapply (wp_wand (Φ := fun v => iprop(∃ (L5 : List E) (new_a : w64),
      "a" ∷ a_ptr ↦ new_a ∗
      "b" ∷ b_ptr ↦ b_val ∗
      "data" ∷ data_ptr ↦ GoInterface.ok x ∗
      "pivot" ∷ pivot_ptr ↦ r3 ∗
      "Hl" ∷ R L5 ∗
      "%ab_range5" ∷ ⌜0 ≤ sint.Z new_a ∧ sint.Z new_a ≤ sint.Z b_val ∧
        sint.Z b_val ≤ l.length⌝ ∗
      "%HPerm5" ∷ ⌜l.Perm L5⌝ ∗
      "%Hpost5" ∷ ⌜v = continueVal ∨ (v = executeVal ∧ L5 = L4 ∧ new_a = a_val)⌝)))
      $$ [a b data pivot Hl]
  · wp_if_destruct
    · list_elem L4 (sint.nat (a_val - W64 1)) as xa
      list_elem L4 (sint.nat r3) as xr
      wp_apply wp_any_Less x R L4 (a_val - W64 1) r3 xa xr (by word) (by word)
        Hxa_lookup Hxr_lookup $$ [$Hs $Hl] as %c Hl
      cases c
      case true =>
        (try wp_auto)
        (try bool_if)
        iexists L4, a_val
        iframe
        ipureintro
        refine ⟨⟨by word, by word, by word⟩, HPerm4, ?_⟩
        first | exact Or.inr ⟨rfl, rfl, rfl⟩ | exact Or.inr ⟨trivial, rfl, rfl⟩
      case false =>
        (try wp_auto)
        (try bool_if)
        wp_apply wp_partitionEqual E x R L4 a_val b_val r3 $$ [Hl]
          with %L5 %new_a ⟨Hl, %HP5, %Hrange5⟩
        · iframe Hl; iframe #; ipureintro; word
        iexists L5, new_a
        iframe
        ipureintro
        refine ⟨⟨by word, by word, by word⟩, HPerm4.trans HP5, ?_⟩
        left; rfl
    · iexists L4, a_val
      iframe
      ipureintro
      refine ⟨⟨by word, by word, by word⟩, HPerm4, ?_⟩
      first | exact Or.inr ⟨rfl, rfl, rfl⟩ | exact Or.inr ⟨trivial, rfl, rfl⟩
  iintro %v ⟨%L5, %new_a, Hpost⟩
  iNamed Hpost
  rcases Hpost5 with Hv | ⟨Hv, HL5, Hnew_a⟩
  · -- `continue` after partitioning out the elements equal to the pivot
    subst Hv
    wp_auto
    wp_for_post
    iframe
    iexists new_a, b_val, limit1, bl1, bl2, L5
    iframe
    ipureintro
    exact ⟨ab_range5, HPerm5⟩
  subst Hv
  subst L5
  subst new_a
  clear HPerm5 ab_range5
  wp_auto
  wp_apply wp_partition E x R L4 a_val b_val r3 $$ [Hl]
    with %L6 %bl %r1 ⟨Hl, %HP6, %rrange1⟩
  · iframe Hl; iframe #; ipureintro; word
  have HPerm6 := HPerm4.trans HP6
  have Hlen6 := HPerm6.length_eq
  -- (unhidden before the pure steps of the `if`, which strip its `▷`)
  irevert IH
  iapply anyHide_elim
  iintro #IH
  wp_if_destruct
  · -- recurse on the (smaller) left part
    rw [func_unfold]
    wp_apply IH $$ %L6 %a_val %r1 %limit1 [Hl] with %L7 ⟨Hl, %HP7⟩
    · iframe Hl; iframe #; ipureintro; word
    wp_for_post
    iframe
    iexists (r1 + W64 1), b_val, limit1, bl, _, L7
    iframe
    ipureintro
    exact ⟨⟨by word, by word, by word⟩, HPerm6.trans HP7⟩
  · -- recurse on the (smaller) right part
    rw [func_unfold]
    wp_apply IH $$ %L6 %(r1 + W64 1) %b_val %limit1 [Hl] with %L7 ⟨Hl, %HP7⟩
    · iframe Hl; iframe #; ipureintro; word
    wp_for_post
    iframe
    iexists a_val, r1, limit1, bl, _, L7
    iframe
    ipureintro
    exact ⟨⟨by word, by word, by word⟩, HPerm6.trans HP7⟩

end proof

end EtcdGrove
end Perennial
