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
open github_com.emirpasic.gods.maps.treemap (cmpOk sortedE Entries lookupE putE sortedE_putE idxOf)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [redblacktree.Assumptions] [go.BasicIntoValInj]

theorem fixPost_mono (tr : Loc) (enc : w64 → GoInterface) (cmp : GoFunc) {T T' : RB GoInterface}
    (D : List Loc) (he : T'.entries = T.entries) :
    fixPost (GF := GF) tr enc cmp T' D ⊢ fixPost tr enc cmp T D := by
  unfold fixPost
  iintro ⟨%T'', %h'', Hraw, %Hp⟩
  iexists T'', h''
  iframe
  ipureintro
  exact ⟨Hp.1.trans he, Hp.2⟩

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


theorem Tree.insertCase4.wp_proof (wp_gp : Node.grandparent.spec (GF := GF))
    (wp_rotL : Tree.rotateLeft.spec (GF := GF)) (wp_rotR : Tree.rotateRight.spec (GF := GF))
    (wp_ic5 : Tree.insertCase5.spec (GF := GF)) :
    Tree.insertCase4.spec (GF := GF) := by
  intro tr enc cmp f1 f2 C h D S
  wp_start as ⟨Hraw, %Hpre⟩
  obtain ⟨hS, hrb⟩ := Hpre
  ihave ⟨Hraw, %Hp⟩ := treeRaw_pure tr enc cmp _ h D $$ Hraw
  obtain ⟨hrep, hperm, hnd⟩ := Hp
  have hndT := hperm.nodup_iff.mp hnd
  cases S with
  | leaf => exact absurd rfl hS
  | node n k v L R =>
  simp only [RB.loc_node]
  have hrep' := hrep
  obtain ⟨hhn, hnn, hL, hR, hC⟩ := Rep_plug_node hrep'
  obtain ⟨hndt, hndC, hdis⟩ := nodup_plug hndT
  have hnD : n ∈ D := hperm.symm.subset (mem_plug (by simp))
  -- the parent and the grandparent
  obtain ⟨hf1, hf2, hC''⟩ := hC
  simp only [Ctx.parent_cons] at hhn hf1
  have hpD : f1.loc ∈ D := hperm.symm.subset (mem_plug_ctx (frame_loc_mem (C := f1 :: f2 :: C) rfl))
  have hgD : f2.loc ∈ D := hperm.symm.subset (mem_plug_ctx (by
    simp only [Ctx.locs, List.mem_append]; right; left; cases f2 <;> simp [Frame.locs, Frame.loc]))
  have hnP : (h n).Parent' = f1.loc := by rw [hhn]
  have hpn : f1.loc ≠ null := by cases f1 <;> exact hf1.1
  have hgn : f2.loc ≠ null := by cases f2 <;> exact hf2.1
  have hpP : (h f1.loc).Parent' = f2.loc := by
    cases f1 with
    | L => obtain ⟨-, hh, -⟩ := hf1; exact congrArg Node.Parent' hh
    | R => obtain ⟨-, hh, -⟩ := hf1; exact congrArg Node.Parent' hh
  iunfold treeRaw at Hraw
  icases Hraw with ⟨%sz, Htr, Hns, -⟩
  wp_auto
  wp_apply (wp_gp h D n) $$ [$Hns]
  · ipureintro; rw [hnP]; exact ⟨hnD, hnn, hpD, hpn⟩
  iintro Hns
  rw [hnP, hpP]
  wp_auto
  cases f1 with
  | R p kp vp PL =>
    cases f2 with
    | L g kg vg U =>
      -- the zig-zag: rotate left at the parent, then the parent is the new node's left child
      obtain ⟨-, hhp, hPL⟩ := hf1
      obtain ⟨-, hhg, hU⟩ := hf2
      simp only [Frame.loc] at hpD hgD hpn hgn hhn hhp hhg ⊢
      have hv_n : h n = nodeOf enc k v (h n).color' L.loc R.loc p := hhn
      ihave ⟨Hn, Hback⟩ := ownNodes_read' h D n _ hnD hv_n $$ Hns
      wp_auto
      ihave Hns := Hback $$ Hn
      ihave ⟨Hp, Hback⟩ := ownNodes_read' h D p _ hpD hhp $$ Hns
      wp_auto
      ihave Hns := Hback $$ Hp
      ihave ⟨Hn, Hback⟩ := ownNodes_read' h D n _ hnD hv_n $$ Hns
      wp_auto
      ihave Hns := Hback $$ Hn
      ihave ⟨Hg, Hback⟩ := ownNodes_read' h D g _ hgD hhg $$ Hns
      wp_auto
      ihave Hns := Hback $$ Hg
      ihave ⟨Hn, Hback⟩ := ownNodes_read' h D n _ hnD hv_n $$ Hns
      wp_auto
      ihave Hns := Hback $$ Hn
      have hT : Ctx.plug (.R p kp vp PL :: .L g kg vg U :: C) (.node n k v L R) =
        Ctx.plug (.L g kg vg U :: C) (.node p kp vp PL (.node n k v L R)) := rfl
      rw [hT] at hrep hperm hrb ⊢
      wp_apply (wp_rotL tr enc cmp (.L g kg vg U :: C) h D p kp vp PL n k v L R) $$ [Htr Hns]
      · iapply (treeRaw_of tr enc cmp _ h D sz ⟨hrep, hperm, hnd⟩); iframe
      iintro ⟨%h1, Hraw, %Hcol⟩
      have hT1 : Ctx.plug (.L g kg vg U :: C) (.node n k v (.node p kp vp PL L) R) =
        Ctx.plug (.L n k v R :: .L g kg vg U :: C) (.node p kp vp PL L) := rfl
      rw [hT1]
      ihave ⟨Hraw, %Hp1⟩ := treeRaw_pure tr enc cmp _ h1 D $$ Hraw
      obtain ⟨hrep1, -, -⟩ := Hp1
      have hrep1' := hrep1
      rw [← hT1] at hrep1'
      obtain ⟨hh1n, -⟩ := Rep_plug_node hrep1'
      iunfold treeRaw at Hraw
      icases Hraw with ⟨%sz1, Htr, Hns, %Hq⟩
      ihave ⟨Hn, Hback⟩ := ownNodes_read' h1 D n _ hnD hh1n $$ Hns
      wp_auto
      ihave Hns := Hback $$ Hn
      wp_apply (wp_ic5 tr enc cmp (.L n k v R) (.L g kg vg U) C h1 D (.node p kp vp PL L)) $$ [Htr Hns]
      · isplitl
        · iapply (treeRaw_of tr enc cmp _ h1 D sz1 Hq); iframe
        ipureintro
        refine ⟨by simp, trivial, rootBlack_congr Hcol ?_ hrb⟩
        rw [← hT1, ← hT]
        exact Ctx.plug_loc_cons _ C _ _
      iintro Hfix
      wp_auto
      iapply HΦ
      iapply (fixPost_mono tr enc cmp
        (T := Ctx.plug (.L g kg vg U :: C) (.node p kp vp PL (.node n k v L R)))
        (T' := Ctx.plug (.L n k v R :: .L g kg vg U :: C) (.node p kp vp PL L)) D (by
        rw [Ctx.plug_entries, Ctx.plug_entries]; simp [Ctx.pre, Ctx.post, Frame.pre, Frame.post]))
      iexact Hfix
    | R g kg vg U =>
      -- zig-zig on the right: no rotation
      obtain ⟨-, hhp, hPL⟩ := hf1
      obtain ⟨-, hhg, hU⟩ := hf2
      simp only [Frame.loc] at hpD hgD hpn hgn hhn hhp hhg ⊢
      have hv_n : h n = nodeOf enc k v (h n).color' L.loc R.loc p := hhn
      simp only [Ctx.locs, Frame.locs, List.nodup_append, List.nodup_cons, List.mem_append,
        List.mem_cons] at hndC hdis
      have hPLn : n ≠ PL.loc := ne_loc_of_not_mem hnn (fun hm => hdis n (by simp) (by simp [hm]))
      have hUp : p ≠ U.loc := ne_loc_of_not_mem hpn (fun hm => by grind)
      ihave ⟨Hn, Hback⟩ := ownNodes_read' h D n _ hnD hv_n $$ Hns
      wp_auto
      ihave Hns := Hback $$ Hn
      ihave ⟨Hp, Hback⟩ := ownNodes_read' h D p _ hpD hhp $$ Hns
      wp_auto
      ihave Hns := Hback $$ Hp
      ihave ⟨Hn, Hback⟩ := ownNodes_read' h D n _ hnD hv_n $$ Hns
      wp_auto
      ihave Hns := Hback $$ Hn
      ihave ⟨Hg, Hback⟩ := ownNodes_read' h D g _ hgD hhg $$ Hns
      wp_auto
      ihave Hns := Hback $$ Hg
      simp only [hUp, _root_.decide_false]
      wp_auto
      ihave ⟨Hn, Hback⟩ := ownNodes_read' h D n _ hnD hv_n $$ Hns
      wp_auto
      ihave Hns := Hback $$ Hn
      ihave ⟨Hp, Hback⟩ := ownNodes_read' h D p _ hpD hhp $$ Hns
      wp_auto
      ihave Hns := Hback $$ Hp
      simp only [hPLn, _root_.decide_false]
      wp_auto
      have wp5 := wp_ic5 tr enc cmp (.R p kp vp PL) (.R g kg vg U) C h D (.node n k v L R)
      simp only [RB.loc_node] at wp5
      wp_apply wp5 $$ [Htr Hns]
      · isplitl
        · iapply (treeRaw_of tr enc cmp _ h D sz ⟨hrep, hperm, hnd⟩); iframe
        ipureintro
        exact ⟨by simp, trivial, hrb⟩
      iintro Hfix
      wp_auto
      iapply HΦ
      iexact Hfix
  | L p kp vp PR =>
    obtain ⟨-, hhp, hPR⟩ := hf1
    simp only [Frame.loc] at hpD hpn hhn hhp ⊢
    have hv_n : h n = nodeOf enc k v (h n).color' L.loc R.loc p := hhn
    have hPRn : n ≠ PR.loc := ne_loc_of_not_mem hnn (fun hm => hdis n (by simp)
      (by simp [Ctx.locs, Frame.locs, hm]))
    ihave ⟨Hn, Hback⟩ := ownNodes_read' h D n _ hnD hv_n $$ Hns
    wp_auto
    ihave Hns := Hback $$ Hn
    ihave ⟨Hp, Hback⟩ := ownNodes_read' h D p _ hpD hhp $$ Hns
    wp_auto
    ihave Hns := Hback $$ Hp
    simp only [hPRn, _root_.decide_false]
    wp_auto
    ihave ⟨Hn, Hback⟩ := ownNodes_read' h D n _ hnD hv_n $$ Hns
    wp_auto
    ihave Hns := Hback $$ Hn
    ihave ⟨Hp, Hback⟩ := ownNodes_read' h D p _ hpD hhp $$ Hns
    wp_auto
    ihave Hns := Hback $$ Hp
    ihave ⟨Hn, Hback⟩ := ownNodes_read' h D n _ hnD hv_n $$ Hns
    wp_auto
    ihave Hns := Hback $$ Hn
    cases f2 with
    | R g kg vg U =>
      -- the zig-zag: rotate right at the parent, then the parent is the new node's right child
      obtain ⟨-, hhg, hU⟩ := hf2
      simp only [Frame.loc] at hgD hgn hhg ⊢
      ihave ⟨Hg, Hback⟩ := ownNodes_read' h D g _ hgD hhg $$ Hns
      wp_auto
      ihave Hns := Hback $$ Hg
      ihave ⟨Hn, Hback⟩ := ownNodes_read' h D n _ hnD hv_n $$ Hns
      wp_auto
      ihave Hns := Hback $$ Hn
      have hT : Ctx.plug (.L p kp vp PR :: .R g kg vg U :: C) (.node n k v L R) =
        Ctx.plug (.R g kg vg U :: C) (.node p kp vp (.node n k v L R) PR) := rfl
      rw [hT] at hrep hperm hrb ⊢
      wp_apply (wp_rotR tr enc cmp (.R g kg vg U :: C) h D p kp vp n k v L R PR) $$ [Htr Hns]
      · iapply (treeRaw_of tr enc cmp _ h D sz ⟨hrep, hperm, hnd⟩); iframe
      iintro ⟨%h1, Hraw, %Hcol⟩
      have hT1 : Ctx.plug (.R g kg vg U :: C) (.node n k v L (.node p kp vp R PR)) =
        Ctx.plug (.R n k v L :: .R g kg vg U :: C) (.node p kp vp R PR) := rfl
      rw [hT1]
      ihave ⟨Hraw, %Hp1⟩ := treeRaw_pure tr enc cmp _ h1 D $$ Hraw
      obtain ⟨hrep1, -, -⟩ := Hp1
      have hrep1' := hrep1
      rw [← hT1] at hrep1'
      obtain ⟨hh1n, -⟩ := Rep_plug_node hrep1'
      iunfold treeRaw at Hraw
      icases Hraw with ⟨%sz1, Htr, Hns, %Hq⟩
      ihave ⟨Hn, Hback⟩ := ownNodes_read' h1 D n _ hnD hh1n $$ Hns
      wp_auto
      ihave Hns := Hback $$ Hn
      wp_apply (wp_ic5 tr enc cmp (.R n k v L) (.R g kg vg U) C h1 D (.node p kp vp R PR)) $$ [Htr Hns]
      · isplitl
        · iapply (treeRaw_of tr enc cmp _ h1 D sz1 Hq); iframe
        ipureintro
        refine ⟨by simp, trivial, rootBlack_congr Hcol ?_ hrb⟩
        rw [← hT1, ← hT]
        exact Ctx.plug_loc_cons _ C _ _
      iintro Hfix
      wp_auto
      iapply HΦ
      iapply (fixPost_mono tr enc cmp
        (T := Ctx.plug (.R g kg vg U :: C) (.node p kp vp (.node n k v L R) PR))
        (T' := Ctx.plug (.R n k v L :: .R g kg vg U :: C) (.node p kp vp R PR)) D (by
        rw [Ctx.plug_entries, Ctx.plug_entries]; simp [Ctx.pre, Ctx.post, Frame.pre, Frame.post]))
      iexact Hfix
    | L g kg vg U =>
      -- zig-zig on the left: no rotation
      obtain ⟨-, hhg, hU⟩ := hf2
      simp only [Frame.loc] at hgD hgn hhg ⊢
      simp only [Ctx.locs, Frame.locs, List.nodup_append, List.nodup_cons, List.mem_append,
        List.mem_cons] at hndC
      have hUp : p ≠ U.loc := ne_loc_of_not_mem hpn (fun hm => by grind)
      ihave ⟨Hg, Hback⟩ := ownNodes_read' h D g _ hgD hhg $$ Hns
      wp_auto
      ihave Hns := Hback $$ Hg
      simp only [hUp, _root_.decide_false]
      wp_auto
      have wp5 := wp_ic5 tr enc cmp (.L p kp vp PR) (.L g kg vg U) C h D (.node n k v L R)
      simp only [RB.loc_node] at wp5
      wp_apply wp5 $$ [Htr Hns]
      · isplitl
        · iapply (treeRaw_of tr enc cmp _ h D sz ⟨hrep, hperm, hnd⟩); iframe
        ipureintro
        exact ⟨by simp, trivial, hrb⟩
      iintro Hfix
      wp_auto
      iapply HΦ
      iexact Hfix

theorem Tree.insertCase1.wp_proof (wp_nc : nodeColor.spec (GF := GF))
    (wp_uncle : Node.uncle.spec (GF := GF)) (wp_gp : Node.grandparent.spec (GF := GF))
    (wp_ic4 : Tree.insertCase4.spec (GF := GF)) :
    Tree.insertCase1.spec (GF := GF) := by
  intro tr enc cmp C h D n k v L R
  iloeb as IH generalizing %C %h %n %k %v %L %R
  wp_start as ⟨Hraw, %Hpre⟩
  ihave ⟨Hraw, %Hp⟩ := treeRaw_pure tr enc cmp _ h D $$ Hraw
  obtain ⟨hrep, hperm, hnd⟩ := Hp
  have hndT := hperm.nodup_iff.mp hnd
  have hrep0 := hrep
  obtain ⟨hhn, hnn, hL, hR, hC⟩ := Rep_plug_node hrep0
  have hnD : n ∈ D := hperm.symm.subset (mem_plug (by simp))
  iunfold treeRaw at Hraw
  icases Hraw with ⟨%sz, Htr, Hns, -⟩
  ihave ⟨Hn, Hback⟩ := ownNodes_read' h D n _ hnD hhn $$ Hns
  wp_auto
  wp_if_destruct
  · -- the root: black
    have hC0 : C = [] := by
      cases C with
      | nil => rfl
      | cons f C' => exact absurd Hif (RepC_parent_ne_null hC (by simp))
    subst hC0
    ihave Hns := Hback $$ Hn
    ihave ⟨Hn, Hback⟩ := ownNodes_acc h D n hnD hnd $$ Hns
    dsimp only [black]
    wp_auto
    ihave Hns := Hback $$ Hn
    iapply HΦ
    iunfold fixPost
    iexists _, _
    isplitl
    · iapply (treeRaw_of tr enc cmp _ _ D sz ⟨Rep_recolor n true hrep, hperm, hnd⟩)
      iframe
    ipureintro
    refine ⟨rfl, Or.inr ?_⟩
    simp
  · ihave Hns := Hback $$ Hn
    wp_method_call
    wp_call
    wp_auto
    cases C with
    | nil => exact absurd rfl Hif
    | cons f1 C' =>
    have hrb : rootBlack h (Ctx.plug (f1 :: C') (.node n k v L R)) :=
      Hpre.resolve_right (by simp)
    obtain ⟨hf1, hC'⟩ := hC
    simp only [Ctx.parent_cons] at hhn Hif
    have hpD : f1.loc ∈ D :=
      hperm.symm.subset (mem_plug_ctx (frame_loc_mem (C := f1 :: C') rfl))
    have hpn : f1.loc ≠ null := Hif
    ihave ⟨Hn, Hback⟩ := ownNodes_read' h D n _ hnD hhn $$ Hns
    wp_auto
    ihave Hns := Hback $$ Hn
    wp_apply (wp_nc h D f1.loc) $$ [$Hns]
    · ipureintro; exact Or.inr hpD
    iintro Hns
    rw [if_neg hpn]
    dsimp only [black]
    wp_auto
    wp_if_destruct
    · -- a black parent: done
      iapply HΦ
      iunfold fixPost
      iexists _, h
      isplitl
      · iapply (treeRaw_of tr enc cmp _ h D sz ⟨hrep, hperm, hnd⟩); iframe
      ipureintro; exact ⟨rfl, hrb⟩
    · -- a red parent: not the root, so a grandparent
      have hpr : (h f1.loc).color' = false := by simpa using Hif
      cases C' with
      | nil =>
        exfalso
        rcases hrb with h0 | h0
        · exact hpn (by simpa [Ctx.plug] using h0)
        · simp [Ctx.plug] at h0; rw [hpr] at h0; exact Bool.false_ne_true h0
      | cons f2 C'' =>
      obtain ⟨hf2, hC''⟩ := hC'
      wp_method_call
      wp_call
      wp_auto
      have hnP : (h n).Parent' = f1.loc := by rw [hhn]
      have hpP : (h f1.loc).Parent' = f2.loc := by
        cases f1 with
        | L => obtain ⟨-, hh, -⟩ := hf1; exact congrArg Node.Parent' hh
        | R => obtain ⟨-, hh, -⟩ := hf1; exact congrArg Node.Parent' hh
      have hgD : f2.loc ∈ D := hperm.symm.subset (mem_plug_ctx (by
        simp only [Ctx.locs, List.mem_append]; right; left; cases f2 <;> simp [Frame.locs, Frame.loc]))
      have hgn : f2.loc ≠ null := by cases f2 <;> exact hf2.1
      obtain ⟨hndt, hndC, hdis⟩ := nodup_plug hndT
      have hf1m : f1.loc ∈ f1.locs := by cases f1 <;> simp [Frame.locs, Frame.loc]
      have hf2m : f2.loc ∈ f2.locs := by cases f2 <;> simp [Frame.locs, Frame.loc]
      simp only [Ctx.locs, List.nodup_append] at hndC
      have hpf2 : f1.loc ∉ f2.locs := fun hm => hndC.2.2 _ hf1m _ (by simp [hm]) rfl
      have hu := uncle_loc hf2 hpn hpf2
      wp_apply (wp_uncle h D n) $$ [$Hns]
      · ipureintro; rw [hnP, hpP]; exact ⟨hnD, hnn, hpD, hpn, hgD, hgn⟩
      iintro Hns
      rw [hnP, hpP, hu]
      wp_auto
      have huD : f2.sib.loc = null ∨ f2.sib.loc ∈ D := by
        rcases loc_null_or_mem f2.sib with h0 | h0
        · left; exact h0
        · right
          exact hperm.symm.subset (mem_plug_ctx (by
            simp only [Ctx.locs, List.mem_append]; right; left; exact Frame.sib_locs_sub f2 _ h0))
      wp_apply (wp_nc h D f2.sib.loc) $$ [$Hns]
      · ipureintro; exact huD
      iintro Hns
      dsimp only [red]
      wp_auto
      wp_if_destruct
      · -- a red uncle: recolor, then up to the grandparent
        have hun : f2.sib.loc ≠ null := by intro e; rw [if_pos e] at Hif; exact Bool.noConfusion Hif
        have hucol : (h f2.sib.loc).color' = false := by rw [if_neg hun] at Hif; exact Hif
        have huD' : f2.sib.loc ∈ D := huD.resolve_left hun
        have hun_mem : f2.sib.loc ∈ f2.sib.locs := (loc_null_or_mem f2.sib).resolve_left hun
        have hu_f2 : f2.sib.loc ∈ f2.locs := Frame.sib_locs_sub f2 _ hun_mem
        have hpu : f1.loc ≠ f2.sib.loc := fun e => hpf2 (e ▸ hu_f2)
        have hpg : f1.loc ≠ f2.loc := fun e => hpf2 (e ▸ hf2m)
        have hug : f2.sib.loc ≠ f2.loc := by
          have hnd2 : f2.locs.Nodup := by
            have h0 := (nodup_plug hndT).2.1
            simp only [Ctx.locs] at h0
            exact (List.nodup_append.mp (List.nodup_append.mp h0).2.1).1
          cases f2 with
          | L g kg vg U =>
            simp only [Frame.locs, List.nodup_cons] at hnd2
            intro e; simp only [Frame.sib, Frame.loc] at e hun_mem; exact hnd2.1 (e ▸ hun_mem)
          | R g kg vg U =>
            simp only [Frame.locs, List.nodup_cons] at hnd2
            intro e; simp only [Frame.sib, Frame.loc] at e hun_mem; exact hnd2.1 (e ▸ hun_mem)
        have hnC : ∀ x ∈ Ctx.locs (f1 :: f2 :: C''), n ≠ x := fun x hx e => hdis n (by simp) (e ▸ hx)
        have hnp : n ≠ f1.loc := hnC _ (by simp [Ctx.locs, hf1m])
        have hnu : n ≠ f2.sib.loc := hnC _ (by simp [Ctx.locs, hu_f2])
        have hng : n ≠ f2.loc := hnC _ (by simp [Ctx.locs, hf2m])
        dsimp only [black]
        ihave ⟨Hn, Hback⟩ := ownNodes_read' h D n _ hnD hhn $$ Hns
        wp_auto
        ihave Hns := Hback $$ Hn
        ihave ⟨Hp, Hback⟩ := ownNodes_acc h D f1.loc hpD hnd $$ Hns
        wp_auto
        ihave Hns := Hback $$ Hp
        have hrep1 := Rep_recolor (enc := enc) f1.loc true hrep
        have hP1 := parent_recolor h f1.loc true
        have hc1 := color_recolor_ne h f1.loc true
        generalize hh1 : upd h f1.loc { h f1.loc with color' := true } = h1 at hrep1 hP1 hc1 ⊢
        ihave ⟨Hu, Hback⟩ := ownNodes_acc h1 D f2.sib.loc huD' hnd $$ Hns
        wp_auto
        ihave Hns := Hback $$ Hu
        have hrep2 := Rep_recolor (enc := enc) f2.sib.loc true hrep1
        have hP2 := parent_recolor h1 f2.sib.loc true
        have hc2 := color_recolor_ne h1 f2.sib.loc true
        generalize hh2 : upd h1 f2.sib.loc { h1 f2.sib.loc with color' := true } = h2
          at hrep2 hP2 hc2 ⊢
        have hP2' : ∀ x, (h2 x).Parent' = (h x).Parent' := fun x => (hP2 x).trans (hP1 x)
        wp_apply (wp_gp h2 D n) $$ [$Hns]
        · ipureintro; simp only [hP2', hnP]; exact ⟨hnD, hnn, hpD, hpn⟩
        iintro Hns
        simp only [hP2', hnP, hpP]
        ihave ⟨Hg, Hback⟩ := ownNodes_acc h2 D f2.loc hgD hnd $$ Hns
        wp_auto
        ihave Hns := Hback $$ Hg
        have hrep3 := Rep_recolor (enc := enc) f2.loc false hrep2
        have hP3 := parent_recolor h2 f2.loc false
        have hc3 := color_recolor_ne h2 f2.loc false
        generalize hh3 : upd h2 f2.loc { h2 f2.loc with color' := false } = h3 at hrep3 hP3 hc3 ⊢
        have hP3' : ∀ x, (h3 x).Parent' = (h x).Parent' := fun x => (hP3 x).trans (hP2' x)
        wp_apply (wp_gp h3 D n) $$ [$Hns]
        · ipureintro; simp only [hP3', hnP]; exact ⟨hnD, hnn, hpD, hpn⟩
        iintro Hns
        simp only [hP3', hnP, hpP]
        -- the grandparent's fix-up: the root is still black, unless it is the grandparent
        have hrbIH : rootBlack h3 (Ctx.plug C'' (f2.fill (f1.fill (.node n k v L R)))) ∨ C'' = [] := by
          cases C'' with
          | nil => right; rfl
          | cons f3 C3 =>
            left
            have hT3 : Ctx.plug (f1 :: f2 :: f3 :: C3) (.node n k v L R) =
              Ctx.plug (f3 :: C3) (f2.fill (f1.fill (.node n k v L R))) := rfl
            have hm := Ctx.plug_loc_mem (C := f3 :: C3) (f2.fill (f1.fill (.node n k v L R))) (by simp)
            have hdis3 := (nodup_plug (C := f3 :: C3) (t := f2.fill (f1.fill (.node n k v L R)))
              (hT3 ▸ hndT)).2.2
            have hpm : f1.loc ∈ (f2.fill (f1.fill (.node n k v L R))).locs :=
              Frame.mem_fill_left _ _ (Frame.mem_fill_right _ _ (Frame.loc_mem_locs f1))
            have hum : f2.sib.loc ∈ (f2.fill (f1.fill (.node n k v L R))).locs :=
              Frame.mem_fill_right _ _ hu_f2
            have hgm : f2.loc ∈ (f2.fill (f1.fill (.node n k v L R))).locs :=
              Frame.mem_fill_right _ _ (Frame.loc_mem_locs f2)
            have hrep3' : Rep enc h (Ctx.plug (f3 :: C3) (f2.fill (f1.fill (.node n k v L R)))) null :=
              hT3 ▸ hrep
            have hrl : (Ctx.plug (f3 :: C3) (f2.fill (f1.fill (.node n k v L R)))).loc ≠ null :=
              Rep_locs_ne_null _ _ hrep3' _ (mem_plug_ctx hm)
            right
            rw [hc3 _ (fun e => hdis3 _ hgm (e ▸ hm)), hc2 _ (fun e => hdis3 _ hum (e ▸ hm)),
              hc1 _ (fun e => hdis3 _ hpm (e ▸ hm))]
            rcases hrb with h0 | h0
            · exact absurd h0 hrl
            · exact h0
        cases f2 with
        | L g kg vg U =>
          simp only [Frame.loc] at hgD hgn ⊢
          have hTg : Ctx.plug (f1 :: .L g kg vg U :: C'') (.node n k v L R) =
            Ctx.plug C'' (.node g kg vg (f1.fill (.node n k v L R)) U) := rfl
          rw [hTg] at hrep3 hperm ⊢
          try wp_auto
          wp_method_call
          wp_apply IH $$ %C'' %h3 %g %kg %vg %(f1.fill (.node n k v L R)) %U [Htr Hns]
          · isplitl
            · iapply (treeRaw_of tr enc cmp _ h3 D sz ⟨hrep3, hperm, hnd⟩); iframe
            ipureintro; exact hrbIH
          iintro Hfix
          wp_auto
          iapply HΦ
          iexact Hfix
        | R g kg vg U =>
          simp only [Frame.loc] at hgD hgn ⊢
          have hTg : Ctx.plug (f1 :: .R g kg vg U :: C'') (.node n k v L R) =
            Ctx.plug C'' (.node g kg vg U (f1.fill (.node n k v L R))) := rfl
          rw [hTg] at hrep3 hperm ⊢
          try wp_auto
          wp_method_call
          wp_apply IH $$ %C'' %h3 %g %kg %vg %U %(f1.fill (.node n k v L R)) [Htr Hns]
          · isplitl
            · iapply (treeRaw_of tr enc cmp _ h3 D sz ⟨hrep3, hperm, hnd⟩); iframe
            ipureintro; exact hrbIH
          iintro Hfix
          wp_auto
          iapply HΦ
          iexact Hfix
      · -- a black uncle
        have wp4 := wp_ic4 tr enc cmp f1 f2 C'' h D (.node n k v L R)
        simp only [RB.loc_node] at wp4
        wp_apply wp4 $$ [Htr Hns]
        · isplitl
          · iapply (treeRaw_of tr enc cmp _ h D sz ⟨hrep, hperm, hnd⟩); iframe
          ipureintro; exact ⟨by simp, hrb⟩
        iintro Hfix
        wp_auto
        iapply HΦ
        iexact Hfix

theorem Tree.Put.wp_proof (wp_ic1 : Tree.insertCase1.spec (GF := GF)) :
    Tree.Put.spec (GF := GF) := by
  intro tr enc es k v
  wp_start as Htr
  iunfold isTree at Htr
  icases Htr with ⟨%cmp, %T, %h, %D, Hraw, #Hcmp, %Hp⟩
  obtain ⟨hs, hes, hrb⟩ := Hp
  subst hes
  ihave ⟨Hraw, %Hq⟩ := treeRaw_pure tr enc cmp T h D $$ Hraw
  obtain ⟨hrep, hperm, hnd⟩ := Hq
  have hndT := hperm.nodup_iff.mp hnd
  iunfold treeRaw at Hraw
  icases Hraw with ⟨%sz, Htr, Hns, -⟩
  ihave #Hcmp' := Hcmp
  iunfold cmpOk at Hcmp'
  wp_auto
  wp_if_destruct
  · -- an empty tree
    have hT : T = .leaf := (Rep_loc_eq_null hrep).mp Hif
    subst hT
    have hD : D = [] := List.Perm.eq_nil hperm
    subst hD
    wp_apply Hcmp' as %c _
    dsimp only [red]
    ihave ⟨Hl, %Hln⟩ := typedPointsto_not_null_dup _ _ _ $$ «$r0»
    wp_apply (wp_ic1 tr enc cmp [] (upd h «$r0_ptr»
      (Node.mk (enc k) v false null null null)) [«$r0_ptr»] «$r0_ptr» k v .leaf .leaf) $$ [Htr Hns Hl]
    · isplitl
      · iapply (treeRaw_of tr enc cmp (Ctx.plug [] (.node «$r0_ptr» k v .leaf .leaf)) _
          [«$r0_ptr»] sz ⟨(by
            show Rep enc _ (.node «$r0_ptr» k v .leaf .leaf) null
            exact ⟨Hln, by simp [upd_apply, nodeOf], trivial, trivial⟩), by simp, by simp⟩)
        simp only [Ctx.plug_nil, RB.loc_node, ownNodes_cons, ownNodes_nil, upd_same]
        iframe
      ipureintro; right; rfl
    iintro Hfix
    iunfold fixPost at Hfix
    icases Hfix with ⟨%T', %h', Hraw, %Hq⟩
    iunfold treeRaw at Hraw
    icases Hraw with ⟨%sz', Htr, Hns, %Hr⟩
    wp_auto
    have heT' : T'.entries = putE RB.leaf.entries k v := by
      rw [Hq.1]; simp [putE, idxOf]
    have hsT' : sortedE T'.entries := by rw [heT']; exact sortedE_putE _ k v hs
    iapply HΦ
    iapply (isTree_of tr enc cmp T' h' [«$r0_ptr»] _ ⟨hsT', heT', Hq.2⟩)
    isplitl
    · iapply (treeRaw_of tr enc cmp T' h' _ _ Hr); iframe
    iexact Hcmp
  · done

end proof

end Perennial.github_com.emirpasic.gods.trees.redblacktree
