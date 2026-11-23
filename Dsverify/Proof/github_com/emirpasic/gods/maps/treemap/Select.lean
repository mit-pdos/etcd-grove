/-
The proof of gods' treemap `Select` (`Specs.lean`): a new map with the same comparator, filled by
its loop over the map's iterator (`Internal.lean`'s specs, which keep the iterated tree, so that the
map is whole again after the walk).
-/
module

public import Dsverify.Spec.github_com.emirpasic.gods.maps.treemap.Internal
public import Dsverify.Spec.github_com.emirpasic.gods.trees.redblacktree.Specs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.emirpasic.gods.maps.treemap

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.emirpasic.gods.trees.redblacktree (RB isTree treeRaw ownIterT treeRaw_of isTree_of
  putE_between sortedE_split)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [treemap.Assumptions] [go.BasicIntoValInj]

theorem Map.Select.wp_proof (wp_new : trees.redblacktree.NewWith.spec (GF := GF))
    (wp_itT : Map.IteratorT.spec (GF := GF)) (wp_nextT : Iterator.NextT.spec (GF := GF))
    (wp_keyT : Iterator.KeyT.spec (GF := GF)) (wp_valueT : Iterator.ValueT.spec (GF := GF))
    (wp_put : Map.Put.spec (GF := GF) isTreeMapR) :
    Map.Select.spec (GF := GF) isTreeMapR := by
  intro tm enc es f P R Hf
  wp_start as ⟨Hm, HR⟩
  iunfold isTreeMapR at Hm
  icases Hm with ⟨%tr, Hm, Htr⟩
  iunfold isTree at Htr
  icases Htr with ⟨%cmp, %T, %h, %D, Hraw, #Hcmp, %Hp⟩
  obtain ⟨hs, hes, hrb⟩ := Hp
  subst hes
  iunfold treeRaw at Hraw
  icases Hraw with ⟨%sz, Htr, Hns, %Hq⟩
  wp_auto
  wp_apply (wp_new cmp enc) $$ [$Hcmp]
  iintro %tr2 Htr2
  wp_auto
  wp_apply (wp_itT tm tr) $$ [$Hm]
  iintro Hm
  wp_auto
  ihave Hfld := typedPointsto_split _ _ _ $$ iterator
  simp only [TypedPointsto.typedPointstoDef, named]
  icases Hfld with ⟨Hfld, -⟩
  ihave Hit : ownIterTM iterator_ptr tr enc cmp T h D T.entries none $$ [Hfld Htr Hns]
  · unfold ownIterTM ownIterT
    iexists null, W8 0
    iframe
    isplitl
    · iapply (treeRaw_of tr enc cmp T h D sz Hq); iframe
    ipureintro; left; exact ⟨rfl, rfl, rfl⟩
  ihave HI : (∃ (vis rest : Entries) (cur : Option (w64 × GoInterface)),
      "Hit" ∷ ownIterTM iterator_ptr tr enc cmp T h D rest cur ∗
      "Hnew" ∷ isTreeMapR «$r0_ptr» enc (vis.filter (fun e => P e.1)) ∗
      "HR" ∷ R ∗
      "%Hv" ∷ ⌜T.entries = vis ++ rest⌝ : IProp GF) $$ [Hit «$r0» Htr2 HR]
  · iexists [], T.entries, none
    iframe
    isplitl
    · iunfold isTreeMapR; iexists tr2; iframe
    ipureintro; rfl
  wp_for HI
  wp_apply (wp_nextT iterator_ptr tr enc cmp T h D rest cur) $$ [$Hit]
  iintro %b Hb
  cases rest with
  | nil =>
    icases Hb with ⟨%hb, Hit⟩
    subst hb
    rw [if_neg (fun h => Bool.false_ne_true (go.intoVal_inj (of_decide_eq_true h))),
      if_pos (decide_eq_true rfl)]
    wp_auto
    iapply HΦ
    unfold ownIterTM ownIterT
    icases Hit with ⟨%nd, %pos, -, Hraw, -⟩
    isplitl [Hm Hraw]
    · iunfold isTreeMapR
      iexists tr
      iframe
      iapply (isTree_of tr enc cmp T h D T.entries ⟨hs, rfl, hrb⟩)
      iframe
      iexact Hcmp
    iframe
    rw [Hv, List.append_nil]
    iexact Hnew
  | cons e r =>
    icases Hb with ⟨%hb, Hit⟩
    subst hb
    obtain ⟨k, v⟩ := e
    rw [if_pos (decide_eq_true rfl)]
    wp_auto
    have hmem : (k, v) ∈ T.entries := by rw [Hv]; simp
    wp_apply (wp_keyT iterator_ptr tr enc cmp T h D r k v) $$ [$Hit]
    iintro Hit
    wp_auto
    wp_apply (wp_valueT iterator_ptr tr enc cmp T h D r k v) $$ [$Hit]
    iintro Hit
    wp_auto
    wp_apply (Hf k v hmem) $$ [$HR]
    iintro HR
    have hlt : ∀ e ∈ vis.filter (fun e => P e.1), sint.Z e.1 < sint.Z k := by
      intro e he
      have he' := (List.mem_filter.mp he).1
      have hs' := hs
      rw [Hv] at hs'
      exact sortedE_split hs' e he' (k, v) (by simp)
    have hsf : sortedE (vis.filter (fun e => P e.1)) := by
      have hs' := hs
      rw [Hv] at hs'
      exact github_com.emirpasic.gods.maps.treemap.sortedE_filter _ _
        (trees.redblacktree.sortedE_left hs')
    cases hP : P k
    · wp_auto
      wp_for_post
      iframe
      iexists vis ++ [(k, v)], r, some (k, v)
      iframe
      isplitl
      · rw [List.filter_append]; simp [hP]; iexact Hnew
      ipureintro; rw [Hv]; simp
    · wp_auto
      wp_apply (wp_keyT iterator_ptr tr enc cmp T h D r k v) $$ [$Hit]
      iintro Hit
      wp_auto
      wp_apply (wp_valueT iterator_ptr tr enc cmp T h D r k v) $$ [$Hit]
      iintro Hit
      wp_auto
      wp_apply (wp_put «$r0_ptr» enc (vis.filter (fun e => P e.1)) k v) $$ [$Hnew]
      iintro Hnew
      wp_auto
      wp_for_post
      iframe
      iexists vis ++ [(k, v)], r, some (k, v)
      iframe
      isplitl
      · have := putE_between (vis.filter (fun e => P e.1)) [] k v (by simpa using hsf) hlt
          (by simp)
        rw [List.append_nil] at this
        rw [this, List.filter_append]; simp [hP]; iexact Hnew
      ipureintro; rw [Hv]; simp

end proof

end Perennial.github_com.emirpasic.gods.maps.treemap
