/-
The proofs of gods' red-black tree `replaceNode`, `rotateLeft` and `rotateRight` (`Specs.lean`).
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

theorem Tree.replaceNode.wp_proof : Tree.replaceNode.spec (GF := GF) := by
  intro tr rt sz cmp h D old new
  wp_start as ⟨Htr, Hns, %Hpre⟩
  obtain ⟨hnd, hold, hpo, hnew, hpar⟩ := Hpre
  ihave ⟨Ho, Hback⟩ := ownNodes_read h D old hold $$ Hns
  wp_auto
  wp_if_destruct
  · -- `old` is the root
    ihave Hns := Hback $$ Ho
    by_cases hn0 : new = null
    · simp only [hn0, _root_.decide_true, Bool.not_true]
      wp_auto
      iapply HΦ
      rw [replaceRes_root Hif, if_pos rfl]
      dsimp only
      iframe
    · simp only [hn0, _root_.decide_false, Bool.not_false]
      have hnD : new ∈ D := hnew.resolve_left hn0
      ihave ⟨Ho, Hback⟩ := ownNodes_read h D old hold $$ Hns
      wp_auto
      ihave Hns := Hback $$ Ho
      ihave ⟨Hn, Hback⟩ := ownNodes_acc h D new hnD hnd $$ Hns
      wp_auto
      ihave Hns := Hback $$ Hn
      iapply HΦ
      rw [replaceRes_root Hif, if_neg hn0]
      dsimp only
      iframe
  · have hpD : (h old).Parent' ∈ D := (hpar.resolve_left Hif).1
    ihave Hns := Hback $$ Ho
    ihave ⟨Hp, Hback⟩ := ownNodes_read h D _ hpD $$ Hns
    wp_auto
    ihave Hns := Hback $$ Hp
    have hif0 := Hif
    wp_if_destruct
    · -- `old` is its parent's left child
      have hL : (h (h old).Parent').Left' = old := Hif.symm
      ihave ⟨Ho, Hback⟩ := ownNodes_read h D old hold $$ Hns
      wp_auto
      ihave Hns := Hback $$ Ho
      ihave ⟨Hp, Hback⟩ := ownNodes_acc h D _ hpD hnd $$ Hns
      wp_auto
      ihave Hns := Hback $$ Hp
      by_cases hn0 : new = null
      · simp only [hn0, _root_.decide_true, Bool.not_true]
        wp_auto
        iapply HΦ
        rw [replaceRes_left hif0 hL, if_pos rfl]
        dsimp only
        iframe
      · simp only [hn0, _root_.decide_false, Bool.not_false]
        have hnD : new ∈ D := hnew.resolve_left hn0
        ihave ⟨Ho, Hback⟩ := ownNodes_read' _ D old (h old) hold (upd_ne h _ old _ (Ne.symm hpo)) $$ Hns
        wp_auto
        ihave Hns := Hback $$ Ho
        ihave ⟨Hn, Hback⟩ := ownNodes_acc _ D new hnD hnd $$ Hns
        wp_auto
        ihave Hns := Hback $$ Hn
        iapply HΦ
        rw [replaceRes_left hif0 hL, if_neg hn0]
        dsimp only
        iframe
    · -- its right child
      have hL : ¬ (h (h old).Parent').Left' = old := fun e => Hif e.symm
      ihave ⟨Ho, Hback⟩ := ownNodes_read h D old hold $$ Hns
      wp_auto
      ihave Hns := Hback $$ Ho
      ihave ⟨Hp, Hback⟩ := ownNodes_acc h D _ hpD hnd $$ Hns
      wp_auto
      ihave Hns := Hback $$ Hp
      by_cases hn0 : new = null
      · simp only [hn0, _root_.decide_true, Bool.not_true]
        wp_auto
        iapply HΦ
        rw [replaceRes_right hif0 hL, if_pos rfl]
        dsimp only
        iframe
      · simp only [hn0, _root_.decide_false, Bool.not_false]
        have hnD : new ∈ D := hnew.resolve_left hn0
        ihave ⟨Ho, Hback⟩ := ownNodes_read' _ D old (h old) hold (upd_ne h _ old _ (Ne.symm hpo)) $$ Hns
        wp_auto
        ihave Hns := Hback $$ Ho
        ihave ⟨Hn, Hback⟩ := ownNodes_acc _ D new hnD hnd $$ Hns
        wp_auto
        ihave Hns := Hback $$ Hn
        iapply HΦ
        rw [replaceRes_right hif0 hL, if_neg hn0]
        dsimp only
        iframe


theorem Tree.rotateLeft.wp_proof (wp_replace : Tree.replaceNode.spec (GF := GF)) :
    Tree.rotateLeft.spec (GF := GF) := by
  intro tr enc cmp C h D n k v A r k' v' B E
  wp_start as Hraw
  ihave ⟨Hraw, %Hp⟩ := treeRaw_pure tr enc cmp _ h D $$ Hraw
  obtain ⟨hrep, hperm, hnd⟩ := Hp
  have hndT := hperm.nodup_iff.mp hnd
  iunfold treeRaw at Hraw
  icases Hraw with ⟨%sz, Htr, Hns, -⟩
  have hrep0 := hrep
  obtain ⟨hhn, hnn, hA, hR, hC⟩ := Rep_plug_node hrep
  obtain ⟨hrn, hhr, hB, hE⟩ := hR
  obtain ⟨hndt, hndC, hdis⟩ := nodup_plug hndT
  obtain ⟨hnr, hnA, hnB, hnE, hrA, hrB, hrE, hAB, hAE, hBE, -, -, -⟩ := locs_rot_facts hndt
  have hnD : n ∈ D := hperm.symm.subset (mem_plug (by simp))
  have hrD : r ∈ D := hperm.symm.subset (mem_plug (by simp))
  have hnP : (h n).Parent' = Ctx.parent C null := by rw [hhn]
  have hnC : n ∉ Ctx.locs C := hdis n (by simp)
  have hrC : r ∉ Ctx.locs C := hdis r (by simp)
  have hpn : Ctx.parent C null ≠ n := by
    cases C with
    | nil => exact Ne.symm hnn
    | cons f C' => intro e; exact hnC (e ▸ frame_loc_mem rfl)
  have hpr : Ctx.parent C null ≠ r := by
    cases C with
    | nil => exact Ne.symm hrn
    | cons f C' => intro e; exact hrC (e ▸ frame_loc_mem rfl)
  have hpar : Ctx.parent C null = null ∨ (Ctx.parent C null ∈ D ∧
      ((h (Ctx.parent C null)).Left' = n ∨ (h (Ctx.parent C null)).Right' = n)) := by
    cases C with
    | nil => left; rfl
    | cons f C' =>
      right
      obtain ⟨hf, -⟩ := hC
      refine ⟨hperm.symm.subset (mem_plug_ctx (frame_loc_mem rfl)), ?_⟩
      exact (holeSet_eq hf hnn (fun hm => hnC (by simp [Ctx.locs, hm])) r).1
  ihave ⟨Hn, Hback⟩ := ownNodes_read' h D n _ hnD hhn $$ Hns
  wp_auto
  ihave Hns := Hback $$ Hn
  simp only [RB.loc_node]
  wp_apply (wp_replace tr _ sz cmp h D n r) $$ [Htr Hns]
  · iframe; ipureintro
    exact ⟨hnd, hnD, by rw [hnP]; exact hpn, Or.inr hrD, by rw [hnP]; exact hpar⟩
  iintro ⟨Htr, Hns⟩
  obtain ⟨h1n, h1r, h1o, h1p, h1rt⟩ := replaceRes_facts (rt := (Ctx.plug C
    (.node n k v A (.node r k' v' B E))).loc) hnr (by rw [hnP]; exact hpn)
    (by rw [hnP]; exact Ne.symm hpr) hrn
  rw [hnP] at h1r h1o h1p h1rt
  generalize hh1 : (replaceRes (Ctx.plug C (.node n k v A (.node r k' v' B E))).loc h n r).2 = h1
    at h1n h1r h1o h1p ⊢
  rw [h1rt]
  have hr1 : h1 r = nodeOf enc k' v' (h r).color' B.loc E.loc (Ctx.parent C null) := by
    rw [h1r, hhr]
  have hn1 : h1 n = nodeOf enc k v (h n).color' A.loc r (Ctx.parent C null) := by
    rw [h1n, hhn]; rfl
  ihave ⟨Hr, Hback⟩ := ownNodes_read' h1 D r _ hrD hr1 $$ Hns
  wp_auto
  ihave Hns := Hback $$ Hr
  ihave ⟨Hn, Hback⟩ := ownNodes_acc' h1 D n _ hnD hnd hn1 $$ Hns
  wp_auto
  ihave Hns := Hback $$ Hn
  have hroot : (if Ctx.parent C null = null then r
      else (Ctx.plug C (.node n k v A (.node r k' v' B E))).loc) =
      (Ctx.plug C (.node r k' v' (.node n k v A B) E)).loc := by
    cases C with
    | nil => simp
    | cons f C' =>
      rw [if_neg (RepC_parent_ne_null hC (by simp))]
      exact Ctx.plug_loc_cons f C' _ _
  rw [hroot]
  have hpermT : D.Perm (Ctx.plug C (.node r k' v' (.node n k v A B) E)).locs :=
    hperm.trans (Ctx.plug_locs_congr C (rotL_locs_perm n k v A r k' v' B E))
  have hpD : ∀ f C', C = f :: C' → f.loc ≠ n ∧ f.loc ≠ r ∧ (∀ x ∈ B.locs, f.loc ≠ x) := by
    intro f C' hC'
    have hm := frame_loc_mem hC'
    refine ⟨fun e => hnC (e ▸ hm), fun e => hrC (e ▸ hm), fun x hx e => hdis x (by simp [hx]) (e ▸ hm)⟩
  cases B with
  | leaf =>
    ihave ⟨Hr, Hback⟩ := ownNodes_acc' _ D r
      (nodeOf enc k' v' (h r).color' RB.leaf.loc E.loc (Ctx.parent C null)) hrD hnd
      (by rw [upd_apply, if_neg (Ne.symm hnr)]; exact hr1) $$ Hns
    wp_auto
    ihave Hns := Hback $$ Hr
    ihave ⟨Hn, Hback⟩ := ownNodes_acc _ D n hnD hnd $$ Hns
    wp_auto
    ihave Hns := Hback $$ Hn
    iapply HΦ
    iexists _
    isplitl
    · iapply (treeRaw_of tr enc cmp _ _ D sz ⟨?_, hpermT, hnd⟩)
      rotate_left
      · iframe
      refine Rep_rotL hrep0 hndT _ ?_ ?_ ?_ ?_ ?_
      · simp [upd_apply, hnr]
      · simp [upd_apply, hnr, Ne.symm hnr]
      · intro b kb vb BL BR e; cases e
      · intro f C' hC'
        obtain ⟨hfn1, hfr1, -⟩ := hpD f C' hC'
        subst hC'
        obtain ⟨hf, hC'⟩ := hC
        have hfn : f.loc ≠ null := RepC_parent_ne_null (C := f :: C') ⟨hf, hC'⟩ (by simp)
        simp only [Ctx.parent_cons] at h1p
        simp only [upd_apply, if_neg hfn1, if_neg hfr1]
        rw [h1p hfn]
        exact ((holeSet_eq hf hnn (fun hm => hnC (by simp [Ctx.locs, hm])) r).2).symm
      · intro l hl1 hl2 _ hl4
        simp only [upd_apply, if_neg hl1, if_neg hl2]
        apply h1o l _ hl2
        cases C with
        | nil => right; rfl
        | cons f C' => left; exact hl4 f C' rfl
    · ipureintro
      have hc1 : ∀ y, (h1 y).color' = (h y).color' := fun y => hh1 ▸ replaceRes_color _ h n r y
      repeat (first | exact hc1 | refine color_upd' ?_ ?_)
      all_goals first
        | rfl
        | (simp [hc1, upd_apply, hnr, Ne.symm hnr]; done)
        | (simp [hc1, upd_apply, hnr, Ne.symm hnr, hbr', Ne.symm hbr', hbn', Ne.symm hbn']; done)
  | node b kb vb BL BR =>
    obtain ⟨hbnn, hhb, -, -⟩ := hB
    have hbn' : b ≠ n := fun e => hnB (by simp [e])
    have hbr' : b ≠ r := fun e => hrB (by simp [e])
    have hbD : b ∈ D := hperm.symm.subset (mem_plug (by simp))
    have hbp : b ≠ Ctx.parent C null ∨ Ctx.parent C null = null := by
      cases C with
      | nil => right; rfl
      | cons f C' => left; intro e; exact (hpD f C' rfl).2.2 b (by simp) e.symm
    have hb1 : h1 b = h b := h1o b hbp hbr'
    ihave ⟨Hr, Hback⟩ := ownNodes_read' _ D r
      (nodeOf enc k' v' (h r).color' b E.loc (Ctx.parent C null)) hrD
      (by rw [upd_apply, if_neg (Ne.symm hnr)]; exact hr1) $$ Hns
    wp_auto
    simp only [hbnn, _root_.decide_false, Bool.not_false]
    wp_auto
    ihave Hns := Hback $$ Hr
    ihave ⟨Hb, Hback⟩ := ownNodes_acc' _ D b
      (nodeOf enc kb vb (h b).color' BL.loc BR.loc r) hbD hnd
      (by rw [upd_apply, if_neg hbn', hb1, hhb]) $$ Hns
    wp_auto
    ihave Hns := Hback $$ Hb
    ihave ⟨Hr, Hback⟩ := ownNodes_acc' _ D r
      (nodeOf enc k' v' (h r).color' b E.loc (Ctx.parent C null)) hrD hnd
      (by rw [upd_apply, if_neg (Ne.symm hbr'), upd_apply, if_neg (Ne.symm hnr)]; exact hr1) $$ Hns
    wp_auto
    ihave Hns := Hback $$ Hr
    ihave ⟨Hn, Hback⟩ := ownNodes_acc _ D n hnD hnd $$ Hns
    wp_auto
    ihave Hns := Hback $$ Hn
    iapply HΦ
    iexists _
    isplitl
    · iapply (treeRaw_of tr enc cmp _ _ D sz ⟨?_, hpermT, hnd⟩)
      rotate_left
      · iframe
      refine Rep_rotL hrep0 hndT _ ?_ ?_ ?_ ?_ ?_
      · simp [upd_apply, hnr, Ne.symm hbn']
      · simp [upd_apply, hnr, Ne.symm hnr, Ne.symm hbr']
      · intro b' kb' vb' BL' BR' e
        cases e
        rw [hhb]
        simp [upd_apply, hbn', hbr']
      · intro f C' hC'
        obtain ⟨hfn1, hfr1, hfB⟩ := hpD f C' hC'
        subst hC'
        obtain ⟨hf, hC'⟩ := hC
        have hfn : f.loc ≠ null := RepC_parent_ne_null (C := f :: C') ⟨hf, hC'⟩ (by simp)
        simp only [Ctx.parent_cons] at h1p
        have hfb1 : f.loc ≠ b := hfB b (by simp)
        simp only [upd_apply, if_neg hfn1, if_neg hfr1, if_neg hfb1]
        rw [h1p hfn]
        exact ((holeSet_eq hf hnn (fun hm => hnC (by simp [Ctx.locs, hm])) r).2).symm
      · intro l hl1 hl2 hl3 hl4
        have hl3' : l ≠ b := hl3 b kb vb BL BR rfl
        simp only [upd_apply, if_neg hl1, if_neg hl2, if_neg hl3']
        apply h1o l _ hl2
        cases C with
        | nil => right; rfl
        | cons f C' => left; exact hl4 f C' rfl
    · ipureintro
      have hc1 : ∀ y, (h1 y).color' = (h y).color' := fun y => hh1 ▸ replaceRes_color _ h n r y
      repeat (first | exact hc1 | refine color_upd' ?_ ?_)
      all_goals first
        | rfl
        | (simp [hc1, upd_apply, hnr, Ne.symm hnr]; done)
        | (simp [hc1, upd_apply, hnr, Ne.symm hnr, hbr', Ne.symm hbr', hbn', Ne.symm hbn']; done)


theorem Tree.rotateRight.wp_proof (wp_replace : Tree.replaceNode.spec (GF := GF)) :
    Tree.rotateRight.spec (GF := GF) := by
  intro tr enc cmp C h D n k v r k' v' A B E
  wp_start as Hraw
  ihave ⟨Hraw, %Hp⟩ := treeRaw_pure tr enc cmp _ h D $$ Hraw
  obtain ⟨hrep, hperm, hnd⟩ := Hp
  have hndT := hperm.nodup_iff.mp hnd
  iunfold treeRaw at Hraw
  icases Hraw with ⟨%sz, Htr, Hns, -⟩
  have hrep0 := hrep
  obtain ⟨hhn, hnn, hR, hE, hC⟩ := Rep_plug_node hrep
  obtain ⟨hrn, hhr, hA, hB⟩ := hR
  obtain ⟨hndt, hndC, hdis⟩ := nodup_plug hndT
  obtain ⟨hnr, hnA, hnB, hnE, hrA, hrB, hrE, hAB, hAE, hBE, -, -, -⟩ := locs_rotR_facts hndt
  have hnD : n ∈ D := hperm.symm.subset (mem_plug (by simp))
  have hrD : r ∈ D := hperm.symm.subset (mem_plug (by simp))
  have hnP : (h n).Parent' = Ctx.parent C null := by rw [hhn]
  have hnC : n ∉ Ctx.locs C := hdis n (by simp)
  have hrC : r ∉ Ctx.locs C := hdis r (by simp)
  have hpn : Ctx.parent C null ≠ n := by
    cases C with
    | nil => exact Ne.symm hnn
    | cons f C' => intro e; exact hnC (e ▸ frame_loc_mem rfl)
  have hpr : Ctx.parent C null ≠ r := by
    cases C with
    | nil => exact Ne.symm hrn
    | cons f C' => intro e; exact hrC (e ▸ frame_loc_mem rfl)
  have hpar : Ctx.parent C null = null ∨ (Ctx.parent C null ∈ D ∧
      ((h (Ctx.parent C null)).Left' = n ∨ (h (Ctx.parent C null)).Right' = n)) := by
    cases C with
    | nil => left; rfl
    | cons f C' =>
      right
      obtain ⟨hf, -⟩ := hC
      refine ⟨hperm.symm.subset (mem_plug_ctx (frame_loc_mem rfl)), ?_⟩
      exact (holeSet_eq hf hnn (fun hm => hnC (by simp [Ctx.locs, hm])) r).1
  ihave ⟨Hn, Hback⟩ := ownNodes_read' h D n _ hnD hhn $$ Hns
  wp_auto
  ihave Hns := Hback $$ Hn
  simp only [RB.loc_node]
  wp_apply (wp_replace tr _ sz cmp h D n r) $$ [Htr Hns]
  · iframe; ipureintro
    exact ⟨hnd, hnD, by rw [hnP]; exact hpn, Or.inr hrD, by rw [hnP]; exact hpar⟩
  iintro ⟨Htr, Hns⟩
  obtain ⟨h1n, h1r, h1o, h1p, h1rt⟩ := replaceRes_facts (rt := (Ctx.plug C
    (.node n k v (.node r k' v' A B) E)).loc) hnr (by rw [hnP]; exact hpn)
    (by rw [hnP]; exact Ne.symm hpr) hrn
  rw [hnP] at h1r h1o h1p h1rt
  generalize hh1 : (replaceRes (Ctx.plug C (.node n k v (.node r k' v' A B) E)).loc h n r).2 = h1
    at h1n h1r h1o h1p ⊢
  rw [h1rt]
  have hr1 : h1 r = nodeOf enc k' v' (h r).color' A.loc B.loc (Ctx.parent C null) := by
    rw [h1r, hhr]
  have hn1 : h1 n = nodeOf enc k v (h n).color' r E.loc (Ctx.parent C null) := by
    rw [h1n, hhn]; rfl
  ihave ⟨Hr, Hback⟩ := ownNodes_read' h1 D r _ hrD hr1 $$ Hns
  wp_auto
  ihave Hns := Hback $$ Hr
  ihave ⟨Hn, Hback⟩ := ownNodes_acc' h1 D n _ hnD hnd hn1 $$ Hns
  wp_auto
  ihave Hns := Hback $$ Hn
  have hroot : (if Ctx.parent C null = null then r
      else (Ctx.plug C (.node n k v (.node r k' v' A B) E)).loc) =
      (Ctx.plug C (.node r k' v' A (.node n k v B E))).loc := by
    cases C with
    | nil => simp
    | cons f C' =>
      rw [if_neg (RepC_parent_ne_null hC (by simp))]
      exact Ctx.plug_loc_cons f C' _ _
  rw [hroot]
  have hpermT : D.Perm (Ctx.plug C (.node r k' v' A (.node n k v B E))).locs :=
    hperm.trans (Ctx.plug_locs_congr C (rotR_locs_perm n k v r k' v' A B E))
  have hpD : ∀ f C', C = f :: C' → f.loc ≠ n ∧ f.loc ≠ r ∧ (∀ x ∈ B.locs, f.loc ≠ x) := by
    intro f C' hC'
    have hm := frame_loc_mem hC'
    refine ⟨fun e => hnC (e ▸ hm), fun e => hrC (e ▸ hm), fun x hx e => hdis x (by simp [hx]) (e ▸ hm)⟩
  cases B with
  | leaf =>
    ihave ⟨Hr, Hback⟩ := ownNodes_acc' _ D r
      (nodeOf enc k' v' (h r).color' A.loc RB.leaf.loc (Ctx.parent C null)) hrD hnd
      (by rw [upd_apply, if_neg (Ne.symm hnr)]; exact hr1) $$ Hns
    wp_auto
    ihave Hns := Hback $$ Hr
    ihave ⟨Hn, Hback⟩ := ownNodes_acc _ D n hnD hnd $$ Hns
    wp_auto
    ihave Hns := Hback $$ Hn
    iapply HΦ
    iexists _
    isplitl
    · iapply (treeRaw_of tr enc cmp _ _ D sz ⟨?_, hpermT, hnd⟩)
      rotate_left
      · iframe
      refine Rep_rotR hrep0 hndT _ ?_ ?_ ?_ ?_ ?_
      · simp [upd_apply, hnr]
      · simp [upd_apply, hnr, Ne.symm hnr]
      · intro b kb vb BL BR e; cases e
      · intro f C' hC'
        obtain ⟨hfn1, hfr1, -⟩ := hpD f C' hC'
        subst hC'
        obtain ⟨hf, hC'⟩ := hC
        have hfn : f.loc ≠ null := RepC_parent_ne_null (C := f :: C') ⟨hf, hC'⟩ (by simp)
        simp only [Ctx.parent_cons] at h1p
        simp only [upd_apply, if_neg hfn1, if_neg hfr1]
        rw [h1p hfn]
        exact ((holeSet_eq hf hnn (fun hm => hnC (by simp [Ctx.locs, hm])) r).2).symm
      · intro l hl1 hl2 _ hl4
        simp only [upd_apply, if_neg hl1, if_neg hl2]
        apply h1o l _ hl2
        cases C with
        | nil => right; rfl
        | cons f C' => left; exact hl4 f C' rfl
    · ipureintro
      have hc1 : ∀ y, (h1 y).color' = (h y).color' := fun y => hh1 ▸ replaceRes_color _ h n r y
      repeat (first | exact hc1 | refine color_upd' ?_ ?_)
      all_goals first
        | rfl
        | (simp [hc1, upd_apply, hnr, Ne.symm hnr]; done)
        | (simp [hc1, upd_apply, hnr, Ne.symm hnr, hbr', Ne.symm hbr', hbn', Ne.symm hbn']; done)
  | node b kb vb BL BR =>
    obtain ⟨hbnn, hhb, -, -⟩ := hB
    have hbn' : b ≠ n := fun e => hnB (by simp [e])
    have hbr' : b ≠ r := fun e => hrB (by simp [e])
    have hbD : b ∈ D := hperm.symm.subset (mem_plug (by simp))
    have hbp : b ≠ Ctx.parent C null ∨ Ctx.parent C null = null := by
      cases C with
      | nil => right; rfl
      | cons f C' => left; intro e; exact (hpD f C' rfl).2.2 b (by simp) e.symm
    have hb1 : h1 b = h b := h1o b hbp hbr'
    ihave ⟨Hr, Hback⟩ := ownNodes_read' _ D r
      (nodeOf enc k' v' (h r).color' A.loc b (Ctx.parent C null)) hrD
      (by rw [upd_apply, if_neg (Ne.symm hnr)]; exact hr1) $$ Hns
    wp_auto
    simp only [hbnn, _root_.decide_false, Bool.not_false]
    wp_auto
    ihave Hns := Hback $$ Hr
    ihave ⟨Hb, Hback⟩ := ownNodes_acc' _ D b
      (nodeOf enc kb vb (h b).color' BL.loc BR.loc r) hbD hnd
      (by rw [upd_apply, if_neg hbn', hb1, hhb]) $$ Hns
    wp_auto
    ihave Hns := Hback $$ Hb
    ihave ⟨Hr, Hback⟩ := ownNodes_acc' _ D r
      (nodeOf enc k' v' (h r).color' A.loc b (Ctx.parent C null)) hrD hnd
      (by rw [upd_apply, if_neg (Ne.symm hbr'), upd_apply, if_neg (Ne.symm hnr)]; exact hr1) $$ Hns
    wp_auto
    ihave Hns := Hback $$ Hr
    ihave ⟨Hn, Hback⟩ := ownNodes_acc _ D n hnD hnd $$ Hns
    wp_auto
    ihave Hns := Hback $$ Hn
    iapply HΦ
    iexists _
    isplitl
    · iapply (treeRaw_of tr enc cmp _ _ D sz ⟨?_, hpermT, hnd⟩)
      rotate_left
      · iframe
      refine Rep_rotR hrep0 hndT _ ?_ ?_ ?_ ?_ ?_
      · simp [upd_apply, hnr, Ne.symm hbn']
      · simp [upd_apply, hnr, Ne.symm hnr, Ne.symm hbr']
      · intro b' kb' vb' BL' BR' e
        cases e
        rw [hhb]
        simp [upd_apply, hbn', hbr']
      · intro f C' hC'
        obtain ⟨hfn1, hfr1, hfB⟩ := hpD f C' hC'
        subst hC'
        obtain ⟨hf, hC'⟩ := hC
        have hfn : f.loc ≠ null := RepC_parent_ne_null (C := f :: C') ⟨hf, hC'⟩ (by simp)
        simp only [Ctx.parent_cons] at h1p
        have hfb1 : f.loc ≠ b := hfB b (by simp)
        simp only [upd_apply, if_neg hfn1, if_neg hfr1, if_neg hfb1]
        rw [h1p hfn]
        exact ((holeSet_eq hf hnn (fun hm => hnC (by simp [Ctx.locs, hm])) r).2).symm
      · intro l hl1 hl2 hl3 hl4
        have hl3' : l ≠ b := hl3 b kb vb BL BR rfl
        simp only [upd_apply, if_neg hl1, if_neg hl2, if_neg hl3']
        apply h1o l _ hl2
        cases C with
        | nil => right; rfl
        | cons f C' => left; exact hl4 f C' rfl
    · ipureintro
      have hc1 : ∀ y, (h1 y).color' = (h y).color' := fun y => hh1 ▸ replaceRes_color _ h n r y
      repeat (first | exact hc1 | refine color_upd' ?_ ?_)
      all_goals first
        | rfl
        | (simp [hc1, upd_apply, hnr, Ne.symm hnr]; done)
        | (simp [hc1, upd_apply, hnr, Ne.symm hnr, hbr', Ne.symm hbr', hbn', Ne.symm hbn']; done)

end proof

end Perennial.github_com.emirpasic.gods.trees.redblacktree
