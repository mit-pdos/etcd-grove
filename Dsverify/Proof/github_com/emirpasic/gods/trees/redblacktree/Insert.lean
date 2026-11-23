/-
The proofs of gods' red-black tree insertion: the fix-up `insertCase1`..`insertCase5` and `Put`
(`Specs.lean`). The red-black balance is not proved: only that the entries are kept, the
representation, and the root's color (black), which the fix-up's safety needs.
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
variable [redblacktree.Assumptions] [go.BasicIntoValInj]

theorem Tree.insertCase5.wp_proof (wp_gp : Node.grandparent.spec (GF := GF))
    (wp_rotL : Tree.rotateLeft.spec (GF := GF)) (wp_rotR : Tree.rotateRight.spec (GF := GF)) :
    Tree.insertCase5.spec (GF := GF) := by
  intro tr enc cmp f1 f2 C h D S
  wp_start as ⟨Hraw, %Hpre⟩
  obtain ⟨hS, hside, hrb⟩ := Hpre
  ihave ⟨Hraw, %Hp⟩ := treeRaw_pure tr enc cmp _ h D $$ Hraw
  obtain ⟨hrep, hperm, hnd⟩ := Hp
  have hndT := hperm.nodup_iff.mp hnd
  cases S with
  | leaf => exact absurd rfl hS
  | node n k v L R =>
  cases f1 with
  | L p kp vp PR =>
    cases f2 with
    | R => exact absurd hside id
    | L g kg vg U =>
    have hT : Ctx.plug (.L p kp vp PR :: .L g kg vg U :: C) (.node n k v L R) =
      Ctx.plug C (.node g kg vg (.node p kp vp (.node n k v L R) PR) U) := rfl
    rw [hT] at hrep hperm hndT hrb ⊢
    obtain ⟨hhg, hgn, hP, hU, hC⟩ := Rep_plug_node hrep
    obtain ⟨hpn, hhp, hN, hPR⟩ := hP
    obtain ⟨hnn, hhn, hL, hR⟩ := hN
    obtain ⟨hndt, hndC, hdis⟩ := nodup_plug hndT
    have hng : n ≠ g := by intro e; subst e; simp [List.nodup_append, List.nodup_cons] at hndt <;> grind
    have hnp : n ≠ p := by intro e; subst e; simp [List.nodup_append, List.nodup_cons] at hndt <;> grind
    have hpg : p ≠ g := by intro e; subst e; simp [List.nodup_append, List.nodup_cons] at hndt <;> grind
    have hnD : n ∈ D := hperm.symm.subset (mem_plug (by simp))
    have hpD : p ∈ D := hperm.symm.subset (mem_plug (by simp))
    have hgD : g ∈ D := hperm.symm.subset (mem_plug (by simp))
    have hnP : (h n).Parent' = p := by rw [hhn]
    have hpP : (h p).Parent' = g := by rw [hhp]
    iunfold treeRaw at Hraw
    icases Hraw with ⟨%sz, Htr, Hns, -⟩
    simp only [RB.loc_node]
    ihave ⟨Hn, Hback⟩ := ownNodes_read' h D n _ hnD hhn $$ Hns
    wp_auto
    ihave Hns := Hback $$ Hn
    ihave ⟨Hp, Hback⟩ := ownNodes_acc h D p hpD hnd $$ Hns
    dsimp only [black]
    wp_auto
    ihave Hns := Hback $$ Hp
    have hrep1 := Rep_recolor (enc := enc) p true hrep
    generalize hh1 : upd h p { h p with color' := true } = h1 at hrep1 ⊢
    have h1n : h1 n = h n := by rw [← hh1, upd_ne _ _ _ _ hnp]
    have h1g : h1 g = h g := by rw [← hh1, upd_ne _ _ _ _ (Ne.symm hpg)]
    have h1p : h1 p = { h p with color' := true } := by rw [← hh1, upd_same]
    wp_apply (wp_gp h1 D n) $$ [$Hns]
    · ipureintro; rw [h1n, hnP]; exact ⟨hnD, hnn, hpD, hpn⟩
    iintro Hns
    have hgv : (h1 (h1 n).Parent').Parent' = g := by rw [h1n, hnP, h1p]; exact hpP
    rw [hgv]
    wp_auto
    ihave ⟨Hg, Hback⟩ := ownNodes_acc h1 D g hgD hnd $$ Hns
    dsimp only [red]
    wp_auto
    ihave Hns := Hback $$ Hg
    have hrep2 := Rep_recolor (enc := enc) g false hrep1
    generalize hh2 : upd h1 g { h1 g with color' := false } = h2 at hrep2 ⊢
    have h2n : h2 n = h n := by rw [← hh2, upd_ne _ _ _ _ hng, h1n]
    have h2p : h2 p = { h p with color' := true } := by rw [← hh2, upd_ne _ _ _ _ hpg, h1p]
    have h2g : h2 g = { h g with color' := false } := by rw [← hh2, upd_same, h1g]
    have hv_n : h2 n = nodeOf enc k v (h n).color' L.loc R.loc p := by rw [h2n, hhn]
    have hv_p : h2 p = nodeOf enc kp vp true n PR.loc g := by rw [h2p, hhp]; rfl
    have hv_g : h2 g = nodeOf enc kg vg false p U.loc (Ctx.parent C null) := by rw [h2g, hhg]; rfl
    ihave ⟨Hn, Hback⟩ := ownNodes_read' h2 D n _ hnD hv_n $$ Hns
    wp_auto
    ihave Hns := Hback $$ Hn
    ihave ⟨Hp, Hback⟩ := ownNodes_read' h2 D p _ hpD hv_p $$ Hns
    wp_auto
    ihave Hns := Hback $$ Hp
    ihave ⟨Hn, Hback⟩ := ownNodes_read' h2 D n _ hnD hv_n $$ Hns
    wp_auto
    ihave Hns := Hback $$ Hn
    ihave ⟨Hg, Hback⟩ := ownNodes_read' h2 D g _ hgD hv_g $$ Hns
    wp_auto
    ihave Hns := Hback $$ Hg
    wp_apply (wp_rotR tr enc cmp C h2 D g kg vg p kp vp (.node n k v L R) PR U) $$ [Htr Hns]
    · iapply (treeRaw_of tr enc cmp _ h2 D sz ⟨hrep2, hperm, hnd⟩); iframe
    iintro ⟨%h3, Hraw, %Hcol⟩
    wp_auto
    iapply HΦ
    iunfold fixPost
    iexists _, h3
    iframe
    ipureintro
    refine ⟨by rw [Ctx.plug_entries, Ctx.plug_entries]; simp, ?_⟩
    apply rootBlack_after hrep hdis hrb
    · intro x hx
      have hxp : x ≠ p := fun e => hx (by simp [e])
      have hxg : x ≠ g := fun e => hx (by simp [e])
      rw [Hcol x, ← hh2, upd_ne _ _ _ _ hxg, ← hh1, upd_ne _ _ _ _ hxp]
    · intro _
      simp only [RB.loc_node]
      rw [Hcol p, h2p]
  | R p kp vp PL =>
    cases f2 with
    | L => exact absurd hside id
    | R g kg vg U =>
    have hT : Ctx.plug (.R p kp vp PL :: .R g kg vg U :: C) (.node n k v L R) =
      Ctx.plug C (.node g kg vg U (.node p kp vp PL (.node n k v L R))) := rfl
    rw [hT] at hrep hperm hndT hrb ⊢
    obtain ⟨hhg, hgn, hU, hP, hC⟩ := Rep_plug_node hrep
    obtain ⟨hpn, hhp, hPL, hN⟩ := hP
    obtain ⟨hnn, hhn, hL, hR⟩ := hN
    obtain ⟨hndt, hndC, hdis⟩ := nodup_plug hndT
    have hng : n ≠ g := by intro e; subst e; simp [List.nodup_append, List.nodup_cons] at hndt <;> grind
    have hnp : n ≠ p := by intro e; subst e; simp [List.nodup_append, List.nodup_cons] at hndt <;> grind
    have hpg : p ≠ g := by intro e; subst e; simp [List.nodup_append, List.nodup_cons] at hndt <;> grind
    have hnD : n ∈ D := hperm.symm.subset (mem_plug (by simp))
    have hpD : p ∈ D := hperm.symm.subset (mem_plug (by simp))
    have hgD : g ∈ D := hperm.symm.subset (mem_plug (by simp))
    have hnP : (h n).Parent' = p := by rw [hhn]
    have hpP : (h p).Parent' = g := by rw [hhp]
    iunfold treeRaw at Hraw
    icases Hraw with ⟨%sz, Htr, Hns, -⟩
    simp only [RB.loc_node]
    ihave ⟨Hn, Hback⟩ := ownNodes_read' h D n _ hnD hhn $$ Hns
    wp_auto
    ihave Hns := Hback $$ Hn
    ihave ⟨Hp, Hback⟩ := ownNodes_acc h D p hpD hnd $$ Hns
    dsimp only [black]
    wp_auto
    ihave Hns := Hback $$ Hp
    have hrep1 := Rep_recolor (enc := enc) p true hrep
    generalize hh1 : upd h p { h p with color' := true } = h1 at hrep1 ⊢
    have h1n : h1 n = h n := by rw [← hh1, upd_ne _ _ _ _ hnp]
    have h1g : h1 g = h g := by rw [← hh1, upd_ne _ _ _ _ (Ne.symm hpg)]
    have h1p : h1 p = { h p with color' := true } := by rw [← hh1, upd_same]
    wp_apply (wp_gp h1 D n) $$ [$Hns]
    · ipureintro; rw [h1n, hnP]; exact ⟨hnD, hnn, hpD, hpn⟩
    iintro Hns
    have hgv : (h1 (h1 n).Parent').Parent' = g := by rw [h1n, hnP, h1p]; exact hpP
    rw [hgv]
    wp_auto
    ihave ⟨Hg, Hback⟩ := ownNodes_acc h1 D g hgD hnd $$ Hns
    dsimp only [red]
    wp_auto
    ihave Hns := Hback $$ Hg
    have hrep2 := Rep_recolor (enc := enc) g false hrep1
    generalize hh2 : upd h1 g { h1 g with color' := false } = h2 at hrep2 ⊢
    have h2n : h2 n = h n := by rw [← hh2, upd_ne _ _ _ _ hng, h1n]
    have h2p : h2 p = { h p with color' := true } := by rw [← hh2, upd_ne _ _ _ _ hpg, h1p]
    have h2g : h2 g = { h g with color' := false } := by rw [← hh2, upd_same, h1g]
    have hv_n : h2 n = nodeOf enc k v (h n).color' L.loc R.loc p := by rw [h2n, hhn]
    have hv_p : h2 p = nodeOf enc kp vp true PL.loc n g := by rw [h2p, hhp]; rfl
    have hv_g : h2 g = nodeOf enc kg vg false U.loc p (Ctx.parent C null) := by rw [h2g, hhg]; rfl
    have hPLn : n ≠ PL.loc := by
      intro e
      rcases loc_null_or_mem PL with h0 | h0
      · exact hnn (e.trans h0)
      · rw [← e] at h0; simp at hndt; grind
    ihave ⟨Hn, Hback⟩ := ownNodes_read' h2 D n _ hnD hv_n $$ Hns
    wp_auto
    ihave Hns := Hback $$ Hn
    ihave ⟨Hp, Hback⟩ := ownNodes_read' h2 D p _ hpD hv_p $$ Hns
    wp_auto
    ihave Hns := Hback $$ Hp
    simp only [hPLn, _root_.decide_false]
    wp_auto
    ihave ⟨Hn, Hback⟩ := ownNodes_read' h2 D n _ hnD hv_n $$ Hns
    wp_auto
    ihave Hns := Hback $$ Hn
    ihave ⟨Hp, Hback⟩ := ownNodes_read' h2 D p _ hpD hv_p $$ Hns
    wp_auto
    ihave Hns := Hback $$ Hp
    ihave ⟨Hn, Hback⟩ := ownNodes_read' h2 D n _ hnD hv_n $$ Hns
    wp_auto
    ihave Hns := Hback $$ Hn
    ihave ⟨Hg, Hback⟩ := ownNodes_read' h2 D g _ hgD hv_g $$ Hns
    wp_auto
    ihave Hns := Hback $$ Hg
    wp_apply (wp_rotL tr enc cmp C h2 D g kg vg U p kp vp PL (.node n k v L R)) $$ [Htr Hns]
    · iapply (treeRaw_of tr enc cmp _ h2 D sz ⟨hrep2, hperm, hnd⟩); iframe
    iintro ⟨%h3, Hraw, %Hcol⟩
    wp_auto
    iapply HΦ
    iunfold fixPost
    iexists _, h3
    iframe
    ipureintro
    refine ⟨by rw [Ctx.plug_entries, Ctx.plug_entries]; simp, ?_⟩
    apply rootBlack_after hrep hdis hrb
    · intro x hx
      have hxp : x ≠ p := fun e => hx (by simp [e])
      have hxg : x ≠ g := fun e => hx (by simp [e])
      rw [Hcol x, ← hh2, upd_ne _ _ _ _ hxg, ← hh1, upd_ne _ _ _ _ hxp]
    · intro _
      simp only [RB.loc_node]
      rw [Hcol p, h2p]


end proof

end Perennial.github_com.emirpasic.gods.trees.redblacktree
