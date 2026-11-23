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

end proof

end Perennial.github_com.emirpasic.gods.trees.redblacktree
