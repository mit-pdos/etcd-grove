module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Insert
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__createIntervalNode
public import Spec.go_etcd_io.etcd.pkg.v3.adt.StringAffineComparable__Compare
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalNode__updateMax
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__insertFixup

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3.adt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

theorem adt.intervalTree.Insert.wp_proof
    (h_createIntervalNode : adt.intervalTree.createIntervalNode.spec (GF := GF) (hG := hG))
    (h_StringAffineComparable_Compare :
      adt.StringAffineComparable.Compare.spec (GF := GF) (hG := hG))
    (h_updateMax : adt.intervalNode.updateMax.spec (GF := GF) (hG := hG))
    (h_insertFixup : adt.intervalTree.insertFixup.spec (GF := GF) (hG := hG)) :
    adt.intervalTree.Insert.spec (GF := GF) (hG := hG) := by
  intro t L b e v
  wp_start as ⟨Ht, %hlen⟩
  ihave %Htn := adt.ownIvt_not_null _ _ _ $$ Ht
  unfold adt.ownIvt
  icases Ht with ⟨%tv, %T, Ht, Hsent, Hn, %Hp⟩
  obtain ⟨hTL, hrb, hsorted, hcnt, -⟩ := Hp
  icases adt.ivt_fields _ _ _ $$ Ht with ⟨Hr, Hc, Hs, -⟩
  wp_auto
  wp_apply h_createIntervalNode t tv.sentinel' (DFrac.own 1) b e v $$ [Hs]
    as %z ⟨Hs, %Hzn, Hziv, Hzmx, Hzl, Hzr, Hzp, Hzc⟩
  · iframe
  ihave %Hzs := adt.ownSentinel_ne _ _ _ $$ Hsent Hzp
  icases adt.iv_open _ _ _ _ _ $$ Hziv with ⟨Hzb, Hze, Hzv, Hzivb⟩
  have hz : ∀ a c, sint.Z (W64 (adt.affCmp a c)) = adt.affCmp a c := by
    intro a c; have := adt.affCmp_bounds a c; word
  have hw0 : ∀ a c, W64 (adt.affCmp a c) = W64 0 ↔ adt.affCmp a c = 0 := by
    intro a c; have := adt.affCmp_bounds a c; constructor <;> intro h <;> word
  have h0 : sint.Z (W64 0) = 0 := rfl
  have hvb : decide ((#false : val) = #true) = false :=
    decide_eq_false (fun h => Bool.false_ne_true (go.intoVal_inj h))
  -- the descent: `x` the hole, `y` its parent
  ihave HI : (∃ (x y : Loc) (C : adt.RbCtx adt.Entry) (Tx : adt.RbT adt.Entry),
      "x" ∷ x_ptr ↦ x ∗ "y" ∷ y_ptr ↦ y ∗
      "HC" ∷ adt.ownCtx t tv.sentinel' C x y Tx.maxEnd ∗
      "Hn" ∷ adt.ownNode tv.sentinel' 1 y x Tx ∗
      "%Hd" ∷ ⌜C.plug Tx = T ∧ C.plug (Tx.insertBST ((b, e), v)) = T.insertBST ((b, e), v) ∧
        C.dirOk ((b, e), v)⌝ : IProp GF) $$ [x y Hr Hn]
  · icases adt.ownCtx_root t _ tv.root' T $$ [Hr Hn] with ⟨HC, Hn⟩
    · iframe
    iexists tv.root', tv.sentinel', .top, T
    iframe
    ipureintro; exact ⟨rfl, rfl, trivial⟩
  wp_for HI
  cases Tx with
  | leaf =>
    icases adt.ownNode_leaf_open _ _ _ _ $$ Hn with %Hx
    subst Hx
    simp only [_root_.decide_true, Bool.not_true, hvb, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    ihave %Hpar := adt.ownCtx_parent _ _ _ _ _ _ $$ HC
    wp_join iprop(adt.ownCtx t tv.sentinel' C z y (some e) ∗
        z.[intervalNode, go!"max"] ↦ adt.maxW e ∗
        z.[intervalNode, go!"iv"].[IntervalValue, go!"Ivl"].[Interval, go!"Begin"] ↦
          interface.mkOk StringAffineComparable.ty #b ∗
        z.[intervalNode, go!"iv"].[IntervalValue, go!"Ivl"].[Interval, go!"End"] ↦
          interface.mkOk StringAffineComparable.ty #e ∗
        y_ptr ↦ y ∗ z_ptr ↦ z ∗ ivt_ptr ↦ t ∗
        t.[intervalTree, go!"sentinel"] ↦ tv.sentinel')
      with [HC Hzmx Hzb Hze y z ivt Hs] as ⟨HC, Hzmx, Hzb, Hze, y, z, ivt, Hs⟩
    · -- the tree was empty: `z` is the root
      have hC : C = .top := Hpar.2 rfl
      subst hC
      rw [adt.ownCtx_top t _ tv.sentinel']
      icases HC with ⟨-, Hr⟩
      wp_auto
      isplitl []
      · ipureintro; rfl
      rw [adt.ownCtx_top]
      iframe
      ipureintro; rfl
    · cases C with
      | top => exact absurd (Hpar.1 rfl) Hif
      | inL c C' ye r =>
        rw [adt.ownCtx_inL t _ c C' ye r tv.sentinel']
        icases HC with ⟨%yp, %rp, %Hyn, Hyiv, Hymx, Hyl, Hyr, Hyp, Hyc, Hrn, HC⟩
        icases adt.iv_open _ _ _ _ _ $$ Hyiv with ⟨Hyb, Hye, Hyv, Hyivb⟩
        wp_auto
        wp_apply h_StringAffineComparable_Compare
        have hlt : adt.ivlLt (b, e) ye.1 := Hd.2.2
        wp_join iprop(y.[intervalNode, go!"left"] ↦ z ∗ y_ptr ↦ y ∗ z_ptr ↦ z ∗
            beginCompare_ptr ↦ W64 (adt.affCmp b ye.1.1) ∗
            z.[intervalNode, go!"iv"].[IntervalValue, go!"Ivl"].[Interval, go!"End"] ↦
              interface.mkOk StringAffineComparable.ty #e ∗
            y.[intervalNode, go!"iv"].[IntervalValue, go!"Ivl"].[Interval, go!"End"] ↦
              interface.mkOk StringAffineComparable.ty #ye.1.2)
          with [Hyl y z beginCompare Hze Hye] as ⟨Hyl, y, z, beginCompare, Hze, Hye⟩
        · have hb1 : ¬ adt.affCmp b ye.1.1 < 0 := by rw [hz, h0] at Hif; exact Hif
          wp_if_destruct
          · wp_apply h_StringAffineComparable_Compare
            wp_if_destruct
            · iframe
            · exfalso
              rcases hlt with h | ⟨-, h⟩
              · exact hb1 h
              · rw [hz, h0] at Hif; exact Hif h
          · exfalso
            rcases hlt with h | ⟨h, -⟩
            · exact hb1 h
            · exact Hif ((hw0 _ _).2 h)
        ihave Hyiv := Hyivb $$ [Hyb Hye Hyv]
        · iframe
        icases adt.ownNode_childMax _ _ _ r $$ Hrn with ⟨Hrm, Hrback⟩
        wp_apply h_updateMax t tv.sentinel' C' y yp z rp ye
            (adt.nodeMaxO RbT.leaf.maxEnd ye r.maxEnd) (some e) r.maxEnd Hyn.1
          $$ [HC Hyiv Hymx Hyl Hyr Hyp Hzmx Hrm] as ⟨HC, Hyiv, Hymx, Hyl, Hyr, Hyp, Hzm, Hrm⟩
        · rw [adt.childMax_some]; iframe; ipureintro; exact Hzs
        rw [adt.childMax_some]
        icases Hzm with ⟨-, Hzmx⟩
        ihave Hrn := Hrback $$ Hrm
        isplitl []
        · ipureintro; rfl
        ihave HC : adt.ownCtx t tv.sentinel' (.inL c C' ye r) z y (some e) $$
            [HC Hyiv Hymx Hyl Hyr Hyp Hyc Hrn]
        · rw [adt.ownCtx_inL]
          iexists yp, rp
          iframe
          ipureintro; exact Hyn
        iframe
      | inR c l ye C' =>
        rw [adt.ownCtx_inR t _ c l ye C' tv.sentinel']
        icases HC with ⟨%yp, %lp, %Hyn, Hyiv, Hymx, Hyl, Hyr, Hyp, Hyc, Hln, HC⟩
        icases adt.iv_open _ _ _ _ _ $$ Hyiv with ⟨Hyb, Hye, Hyv, Hyivb⟩
        wp_auto
        wp_apply h_StringAffineComparable_Compare
        have hge : ¬ adt.ivlLt (b, e) ye.1 := Hd.2.2
        wp_join iprop(y.[intervalNode, go!"right"] ↦ z ∗ y_ptr ↦ y ∗ z_ptr ↦ z ∗
            beginCompare_ptr ↦ W64 (adt.affCmp b ye.1.1) ∗
            z.[intervalNode, go!"iv"].[IntervalValue, go!"Ivl"].[Interval, go!"End"] ↦
              interface.mkOk StringAffineComparable.ty #e ∗
            y.[intervalNode, go!"iv"].[IntervalValue, go!"Ivl"].[Interval, go!"End"] ↦
              interface.mkOk StringAffineComparable.ty #ye.1.2)
          with [Hyr y z beginCompare Hze Hye] as ⟨Hyr, y, z, beginCompare, Hze, Hye⟩
        · exfalso
          exact hge (Or.inl (by rw [hz, h0] at Hif; exact Hif))
        · have hb1 : ¬ adt.affCmp b ye.1.1 < 0 := by rw [hz, h0] at Hif; exact Hif
          wp_if_destruct
          · have hb0 := (hw0 _ _).1 Hif
            wp_apply h_StringAffineComparable_Compare
            wp_if_destruct
            · exfalso
              exact hge (Or.inr ⟨hb0, by rw [hz, h0] at Hif; exact Hif⟩)
            · iframe
          · iframe
        ihave Hyiv := Hyivb $$ [Hyb Hye Hyv]
        · iframe
        icases adt.ownNode_childMax _ _ _ l $$ Hln with ⟨Hlm, Hlback⟩
        wp_apply h_updateMax t tv.sentinel' C' y yp lp z ye
            (adt.nodeMaxO l.maxEnd ye RbT.leaf.maxEnd) l.maxEnd (some e) Hyn.1
          $$ [HC Hyiv Hymx Hyl Hyr Hyp Hzmx Hlm] as ⟨HC, Hyiv, Hymx, Hyl, Hyr, Hyp, Hlm, Hzm⟩
        · rw [adt.childMax_some]; iframe; ipureintro; exact Hzs
        rw [adt.childMax_some]
        icases Hzm with ⟨-, Hzmx⟩
        ihave Hln := Hlback $$ Hlm
        isplitl []
        · ipureintro; rfl
        ihave HC : adt.ownCtx t tv.sentinel' (.inR c l ye C') z y (some e) $$
            [HC Hyiv Hymx Hyl Hyr Hyp Hyc Hln]
        · rw [adt.ownCtx_inR]
          iexists yp, lp
          iframe
          ipureintro; exact Hyn
        iframe
    -- `z` red (it is), the fixup, the count
    rw [show red = #(adt.colorW .red) from rfl]
    wp_auto
    ihave Hziv := Hzivb $$ [Hzb Hze Hzv]
    · iframe
    ihave Hz := adt.ownNode_node_close tv.sentinel' 1 y z .red .leaf ((b, e), v) .leaf $$
      [Hziv Hzmx Hzl Hzr Hzp Hzc]
    · iexists tv.sentinel', tv.sentinel'
      rw [adt.ownNode_leaf,
        show adt.nodeMax .leaf ((b, e), v) .leaf = e from rfl]
      dsimp only
      iframe
      ipureintro; exact ⟨⟨Hzs, Hzn⟩, rfl, rfl⟩
    have hfix : C.FixInv (.node .red .leaf ((b, e), v) .leaf) :=
      adt.RbCtx.fixInv_start C _ (by rw [Hd.1]; exact hrb.1) (by rw [Hd.1]; exact hrb.2.1)
        (by rw [Hd.1]; exact hrb.2.2)
    wp_apply h_insertFixup t tv.sentinel' (DFrac.own 1) C z y (.node .red .leaf ((b, e), v) .leaf)
      hfix $$ [Hs HC Hz] as ⟨Hs, %R, %T', Hr, HT', %HT'⟩
    · simp only [adt.maxEnd_node, adt.nodeMax_eq, adt.maxEnd_leaf, adt.nodeMaxO, adt.affMaxO]
      iframe
    ihave Ht := adt.ivt_combine t R tv.sentinel' (tv.count' + W64 1) Htn $$ [Hr Hc Hs]
    · iframe
    iapply HΦ
    iexists ({ root' := R, count' := tv.count' + W64 1, sentinel' := tv.sentinel' } : intervalTree),
      T'
    iframe
    ipureintro
    have hins : (RbCtx.plug C (.node .red .leaf ((b, e), v) .leaf)) =
        T.insertBST ((b, e), v) := Hd.2.1
    refine ⟨?_, HT'.1, adt.ivtInsert_ivSorted _ L hsorted, ?_, ?_⟩
    · rw [HT'.2, hins, adt.inorder_insertBST _ T (by rw [hTL]; exact hsorted), hTL]
    · rw [adt.length_ivtInsert, hcnt]; word
    · rw [adt.length_ivtInsert]; exact hlen
  | node c l xe r =>
    icases adt.ownNode_node_open _ _ _ _ _ _ _ _ $$ Hn with
      ⟨%lp, %rp, %Hxn, Hxiv, Hxmx, Hxl, Hxr, Hxp, Hxc, Hxln, Hxrn⟩
    simp only [decide_false, Hxn.1, Bool.not_false, _root_.decide_true, ↓reduceIte]
    icases adt.iv_open _ _ _ _ _ $$ Hxiv with ⟨Hxb, Hxe, Hxv, Hxivb⟩
    wp_auto
    wp_apply h_StringAffineComparable_Compare
    wp_if_destruct
    · -- begin below: left
      have hlt : adt.ivlLt (b, e) xe.1 := Or.inl (by rw [hz, h0] at Hif; exact Hif)
      wp_for_post
      ihave Hxiv := Hxivb $$ [Hxb Hxe Hxv]
      · iframe
      simp only [adt.maxEnd_node]
      ihave HC := adt.ownCtx_push_inL t _ C x y c l xe r lp rp Hxn $$
        [HC Hxiv Hxmx Hxl Hxr Hxp Hxc Hxrn]
      · iframe
      iframe
      iexists lp, x, .inL c C xe r, l
      iframe
      ipureintro
      refine ⟨by simpa using Hd.1, ?_, hlt⟩
      rw [← Hd.2.1, adt.plug_insertBST_left _ _ _ _ _ _ hlt]
    · have hb1 : ¬ adt.affCmp b xe.1.1 < 0 := by rw [hz, h0] at Hif; exact Hif
      wp_if_destruct
      · have hb0 := (hw0 _ _).1 Hif
        wp_apply h_StringAffineComparable_Compare
        wp_if_destruct
        · -- begin equal, end below: left
          have hlt : adt.ivlLt (b, e) xe.1 := Or.inr ⟨hb0, by rw [hz, h0] at Hif; exact Hif⟩
          wp_for_post
          ihave Hxiv := Hxivb $$ [Hxb Hxe Hxv]
          · iframe
          simp only [adt.maxEnd_node]
          ihave HC := adt.ownCtx_push_inL t _ C x y c l xe r lp rp Hxn $$
            [HC Hxiv Hxmx Hxl Hxr Hxp Hxc Hxrn]
          · iframe
          iframe
          iexists lp, x, .inL c C xe r, l
          iframe
          ipureintro
          refine ⟨by simpa using Hd.1, ?_, hlt⟩
          rw [← Hd.2.1, adt.plug_insertBST_left _ _ _ _ _ _ hlt]
        · -- begin equal, end not below: right
          have hge : ¬ adt.ivlLt (b, e) xe.1 := by
            rintro (h | ⟨-, h⟩)
            · exact hb1 h
            · rw [hz, h0] at Hif; exact Hif h
          wp_for_post
          ihave Hxiv := Hxivb $$ [Hxb Hxe Hxv]
          · iframe
          simp only [adt.maxEnd_node]
          ihave HC := adt.ownCtx_push_inR t _ C x y c l xe r lp rp Hxn $$
            [HC Hxiv Hxmx Hxl Hxr Hxp Hxc Hxln]
          · iframe
          iframe
          iexists rp, x, .inR c l xe C, r
          iframe
          ipureintro
          refine ⟨by simpa using Hd.1, ?_, hge⟩
          rw [← Hd.2.1, adt.plug_insertBST_right _ _ _ _ _ _ hge]
      · -- begin above: right
        have hge : ¬ adt.ivlLt (b, e) xe.1 := by
          rintro (h | ⟨h, -⟩)
          · exact hb1 h
          · exact Hif ((hw0 _ _).2 h)
        wp_for_post
        ihave Hxiv := Hxivb $$ [Hxb Hxe Hxv]
        · iframe
        simp only [adt.maxEnd_node]
        ihave HC := adt.ownCtx_push_inR t _ C x y c l xe r lp rp Hxn $$
          [HC Hxiv Hxmx Hxl Hxr Hxp Hxc Hxln]
        · iframe
        iframe
        iexists rp, x, .inR c l xe C, r
        iframe
        ipureintro
        refine ⟨by simpa using Hd.1, ?_, hge⟩
        rw [← Hd.2.1, adt.plug_insertBST_right _ _ _ _ _ _ hge]

end proof

end EtcdGrove
end Perennial
