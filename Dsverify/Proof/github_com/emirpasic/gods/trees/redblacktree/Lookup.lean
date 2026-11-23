/-
The proofs of gods' red-black tree `lookup` and `Get` (`Specs.lean`).
-/
module

public import Dsverify.Spec.github_com.emirpasic.gods.trees.redblacktree.Specs
public import Dsverify.Proof.github_com.emirpasic.gods.trees.redblacktree.Iter

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.emirpasic.gods.trees.redblacktree

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.emirpasic.gods.maps.treemap (cmpOk sortedE Entries lookupE putE)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [redblacktree.Assumptions]

theorem Tree.lookup.wp_proof : Tree.lookup.spec (GF := GF) := by
  intro tr enc cmp T h D k
  wp_start as ⟨Htr, #Hcmp, %Hs⟩
  ihave ⟨Htr, %Hraw⟩ := treeRaw_pure tr enc cmp T h D $$ Htr
  obtain ⟨hrep, hperm, hnd⟩ := Hraw
  unfold treeRaw
  icases Htr with ⟨%sz, Htr, Hns, -⟩
  ihave #Hcmp' := Hcmp
  iunfold cmpOk at Hcmp'
  wp_auto
  ihave HI : (∃ (C : Ctx GoInterface) (S : RB GoInterface),
      "node" ∷ node_ptr ↦ S.loc ∗ "%HCS" ∷ ⌜T = Ctx.plug C S ∧ Bounds k C⌝ : IProp GF) $$ [node]
  · iexists [], T; iframe; ipureintro; exact ⟨rfl, Bounds_nil k⟩
  wp_for HI
  obtain ⟨hTCS, hb⟩ := HCS
  have hrepS : Rep enc h S (Ctx.parent C null) := ((Rep_plug C S null).mp (hTCS ▸ hrep)).2
  wp_if_destruct
  · have hS : S.loc ≠ null := not_of_not_decide_val (hG := hG) Hif
    cases S with
    | leaf => exact absurd rfl hS
    | node n k' v' L R =>
    simp only [RB.loc_node]
    obtain ⟨-, hh, -, -⟩ := hrepS
    have hmem : n ∈ D := hperm.symm.subset (hTCS ▸ mem_plug (by simp))
    ihave ⟨Hn, Hback⟩ := ownNodes_read' h D n _ hmem hh $$ Hns
    wp_auto
    wp_apply Hcmp' as %cv %Hc
    have hsN := sortedE_plug_node (hTCS ▸ Hs)
    wp_if_destruct
    · -- found
      have hcv : cv = W64 0 := of_decide_eq_true Hif.symm
      have hk : k = k' := Hc.2.mp hcv
      subst hk
      wp_for_post
      ihave Hns := Hback $$ Hn
      iapply HΦ
      isplitl [Htr Hns]
      · iexists sz; iframe; ipureintro; exact ⟨hrep, hperm, hnd⟩
      ipureintro
      right
      refine ⟨C, v', L, R, hTCS, ?_⟩
      rw [hTCS, lookupE_plug C _ k hb]
      exact lookupE_node_self hsN.1
    · have hne0 := Hif
      wp_if_destruct
      · -- below: left
        have hlt : sint.Z k < sint.Z k' := Hc.1.mp (by
          have := of_decide_eq_true Hif.symm; simpa using this)
        ihave Hns := Hback $$ Hn
        wp_for_post
        iframe
        iexists (.L n k' v' R :: C), L
        iframe
        ipureintro
        exact ⟨hTCS, Bounds_left (hTCS ▸ Hs) hb hlt⟩
      · have hnlt0 := Hif
        wp_if_destruct
        · -- above: right
          have hne : cv ≠ W64 0 := fun e => hne0 (by rw [e]; simp)
          have hnlt : ¬ sint.Z k < sint.Z k' := fun hl => hnlt0 (by
            have := Hc.1.mpr hl; simpa using this)
          have hkk : k ≠ k' := fun e => hne (Hc.2.mpr e)
          have hgt : sint.Z k' < sint.Z k := by
            have : sint.Z k ≠ sint.Z k' := fun e => hkk (BitVec.eq_of_toInt_eq e)
            omega
          ihave Hns := Hback $$ Hn
          wp_for_post
          iframe
          iexists (.R n k' v' L :: C), R
          iframe
          ipureintro
          exact ⟨hTCS, Bounds_right (hTCS ▸ Hs) hb hgt⟩
        · exfalso
          have h1 : ¬ cv = W64 0 := fun e => hne0 (by rw [e]; simp)
          have h2 : ¬ sint.Z cv < 0 := fun e => hnlt0 (by simpa using e)
          have h3 : ¬ 0 < sint.Z cv := fun e => Hif (by simpa using e)
          apply h1
          apply BitVec.eq_of_toInt_eq
          simp only [show sint.Z (W64 0) = 0 from rfl] at *
          have : sint.Z cv = 0 := by omega
          exact this
  · -- not found
    have hS : S.loc = null := of_not_not_decide_val (hG := hG) Hif
    rw [if_pos (decide_eq_true (not_decide_val_false (hG := hG) hS))]
    have hSl : S = .leaf := (Rep_loc_eq_null hrepS).mp hS
    subst hSl
    wp_auto
    iapply HΦ
    isplitl [Htr Hns]
    · iexists sz; iframe; ipureintro; exact ⟨hrep, hperm, hnd⟩
    ipureintro
    left
    refine ⟨rfl, ?_⟩
    rw [hTCS, lookupE_plug C _ k hb]
    rfl

theorem Tree.Get.wp_proof (wp_lookup : Tree.lookup.spec (GF := GF)) :
    Tree.Get.spec (GF := GF) := by
  intro tr enc es k
  wp_start as Htr
  iunfold isTree at Htr
  icases Htr with ⟨%cmp, %T, %h, %D, Hraw, #Hcmp, %Hp⟩
  obtain ⟨hs, hes, hcol⟩ := Hp
  subst hes
  wp_auto
  wp_apply (wp_lookup tr enc cmp T h D k) $$ [Hraw]
  · iframe
    isplitr
    · iexact Hcmp
    ipureintro; exact hs
  iintro %n ⟨Hraw, %Hn⟩
  ihave ⟨Hraw, %Hr⟩ := treeRaw_pure tr enc cmp T h D $$ Hraw
  obtain ⟨hrep, hperm, hnd⟩ := Hr
  wp_auto
  by_cases hn : n = null
  · simp only [hn, _root_.decide_true, Bool.not_true]
    wp_auto
    rcases Hn with ⟨-, hnone⟩ | ⟨C, v, L, R, hT, -⟩
    · rw [hnone]
      simp only [Option.getD_none, Option.isSome_none]
      iapply HΦ
      iapply (isTree_of tr enc cmp T h D T.entries ⟨hs, rfl, hcol⟩)
      isplitl [Hraw]
      · iexact Hraw
      iexact Hcmp
    · exfalso
      rw [hT] at hrep
      exact (Rep_plug_node hrep).2.1 hn
  · simp only [hn, _root_.decide_false, Bool.not_false]
    rcases Hn with ⟨hn0, -⟩ | ⟨C, v, L, R, hT, hsome⟩
    · exact absurd hn0 hn
    iunfold treeRaw at Hraw
    icases Hraw with ⟨%sz, Htrp, Hns, -⟩
    have hrep' := hrep
    rw [hT] at hrep'
    obtain ⟨hh, -⟩ := Rep_plug_node hrep'
    have hmem : n ∈ D := hperm.symm.subset (hT ▸ mem_plug_node)
    ihave ⟨Hn, Hback⟩ := ownNodes_read' h D n _ hmem hh $$ Hns
    wp_auto
    ihave Hns := Hback $$ Hn
    rw [hsome]
    simp only [Option.getD_some, Option.isSome_some]
    iapply HΦ
    iapply (isTree_of tr enc cmp T h D T.entries ⟨hs, rfl, hcol⟩)
    isplitl [Htrp Hns]
    · iapply (treeRaw_of tr enc cmp T h D sz ⟨hrep, hperm, hnd⟩); iframe
    iexact Hcmp

end proof

end Perennial.github_com.emirpasic.gods.trees.redblacktree
