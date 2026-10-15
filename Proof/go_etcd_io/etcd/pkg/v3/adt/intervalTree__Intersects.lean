module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Intersects
public import Spec.go_etcd_io.etcd.pkg.v3.adt.Interval__Compare
public import Spec.go_etcd_io.etcd.pkg.v3.adt.StringAffineComparable__Compare
public import Proof.go_etcd_io.etcd.pkg.v3.adt.NodeLemmas

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

theorem adt.intervalTree.Intersects.wp_proof
    (h_Interval_Compare : adt.Interval.Compare.spec (GF := GF) (hG := hG))
    (h_StringAffineComparable_Compare :
      adt.StringAffineComparable.Compare.spec (GF := GF) (hG := hG)) :
    adt.intervalTree.Intersects.spec (GF := GF) (hG := hG) := by
  intro t L b e q
  wp_start as Ht
  icases adt.ownIvt_read _ _ _ $$ Ht with ⟨%tv, %T, Hr, Hc, Hs, Hn, %Hp, Hback⟩
  obtain ⟨hTL, -, hsorted, -⟩ := Hp
  subst hTL
  wp_auto
  ihave HI : (∃ (x p : Loc) (Tx : adt.RbT adt.Entry),
      "x" ∷ x_ptr ↦ x ∗ "Hx" ∷ adt.ownNode tv.sentinel' q p x Tx ∗
      "Hw" ∷ (adt.ownNode tv.sentinel' q p x Tx -∗
        adt.ownNode tv.sentinel' q tv.sentinel' tv.root' T) ∗
      "%Hinv" ∷ ⌜adt.IvSorted Tx.inorder ∧ Tx.intersects (b, e) = T.intersects (b, e)⌝ : IProp GF)
      $$ [x Hn]
  · iexists tv.root', tv.sentinel', T
    iframe
    isplitl []
    · iintro H; iexact H
    ipureintro; exact ⟨hsorted, rfl⟩
  wp_for HI
  have hvf : decide ((#false : val) = #true) = false :=
    decide_eq_false (fun h => Bool.false_ne_true (go.intoVal_inj h))
  have hvt : decide ((#true : val) = #true) = true := decide_eq_true rfl
  have hres : T.intersects (b, e) = decide (adt.stab (b, e) T.inorder ≠ []) := by
    have := adt.intersects_iff (b, e) T hsorted
    cases h : T.intersects (b, e) <;> simp_all
  rw [← hres, ← Hinv.2]
  cases Tx with
  | leaf =>
    icases adt.ownNode_leaf_open _ _ _ _ $$ Hx with %Hx
    subst Hx
    simp only [decide_true, Bool.not_true]
    simp only [adt.RbT.intersects]
    wp_auto
    simp only [hvf, Bool.false_eq_true, _root_.decide_true, ↓reduceIte]
    wp_auto
    iapply HΦ
    iapply Hback
    iframe
    iapply Hw
    iapply adt.ownNode_leaf_close
  | node c l z r =>
    icases adt.ownNode_node_open _ _ _ _ c l z r $$ Hx with
      ⟨%lp, %rp, %Hn, Hiv, Hmx, Hl, Hr', Hp, Hc', Hnl, Hnr⟩
    simp only [decide_false, Hn.1, Bool.not_false]
    icases adt.iv_open_ivl _ _ _ _ _ $$ Hiv with ⟨Hivl, Hivb⟩
    wp_auto
    wp_apply h_Interval_Compare iv_ptr (DFrac.own 1) b e _ (DFrac.own q) z.1.1 z.1.2
      $$ [$Hivl $iv] as ⟨iv, Hivl⟩
    ihave Hiv := Hivb $$ Hivl
    have hic : W64 (adt.ivlCmp (b, e) (z.1.1, z.1.2)) = W64 0 ↔
        adt.ivlCmp (b, e) (z.1.1, z.1.2) = 0 := by
      have : adt.ivlCmp (b, e) (z.1.1, z.1.2) = -1 ∨ adt.ivlCmp (b, e) (z.1.1, z.1.2) = 1 ∨
          adt.ivlCmp (b, e) (z.1.1, z.1.2) = 0 := by
        unfold adt.ivlCmp; split <;> (try split) <;> simp
      rcases this with h | h | h <;> rw [h] <;> decide
    have hz : ∀ a c, sint.Z (W64 (adt.affCmp a c)) = adt.affCmp a c := by
      intro a c; have := adt.affCmp_bounds a c; word
    have h0 : sint.Z (W64 0) = 0 := rfl
    obtain ⟨hsl, hsr, -, -⟩ := adt.ivSorted_node Hinv.1
    have hint := Hinv.2
    -- the node, repacked
    ihave Hpack : (x.[intervalNode, go!"iv"] ↦{DFrac.own q}
          ({ Ivl' := adt.affIvl z.1.1 z.1.2, Val' := z.2 } : IntervalValue) ∗
        x.[intervalNode, go!"max"] ↦{DFrac.own q} adt.maxW (adt.nodeMax l z r) ∗
        x.[intervalNode, go!"left"] ↦{DFrac.own q} lp ∗
        x.[intervalNode, go!"right"] ↦{DFrac.own q} rp ∗
        x.[intervalNode, go!"parent"] ↦{DFrac.own q} p ∗
        x.[intervalNode, go!"c"] ↦{DFrac.own q} adt.colorW c -∗
        adt.ownNode tv.sentinel' q x lp l -∗ adt.ownNode tv.sentinel' q x rp r -∗
        adt.ownNode tv.sentinel' q p x (.node c l z r)) $$ []
    · iintro ⟨Hiv, Hmx, Hl, Hr', Hp, Hc⟩ Hnl Hnr
      iapply adt.ownNode_node_close
      iexists lp, rp
      iframe
      ipureintro; exact Hn
    by_cases hov : adt.ivlCmp (b, e) (z.1.1, z.1.2) = 0
    · -- the node overlaps: stop
      have hd : decide (W64 (adt.ivlCmp (b, e) (z.1.1, z.1.2)) = W64 0) = true :=
        decide_eq_true (hic.2 hov)
      simp only [hd, Bool.not_true, hvf, Bool.false_eq_true, _root_.decide_true, ↓reduceIte]
      wp_auto
      simp only [Hn.1, decide_false, Bool.not_false]
      have ht : (adt.RbT.node c l z r).intersects (b, e) = true := by
        unfold adt.RbT.intersects
        simp only [show adt.ivlCmp (b, e) z.1 = 0 from hov, ↓reduceIte]
      rw [ht]
      iapply HΦ
      iapply Hback
      iframe
      iapply Hw
      iapply Hpack $$ [Hiv Hmx Hl Hr' Hp Hc'] Hnl Hnr
      iframe
    have hd : decide (W64 (adt.ivlCmp (b, e) (z.1.1, z.1.2)) = W64 0) = false :=
      decide_eq_false (fun h => hov (hic.1 h))
    simp only [hd, Bool.not_false, _root_.decide_true, ↓reduceIte]
    wp_auto
    have hnode : ∀ X, X = (adt.RbT.node c l z r).intersects (b, e) →
        X = (match l.maxEnd with
          | some m => if adt.affCmp m b > 0 then l.intersects (b, e) else r.intersects (b, e)
          | none => r.intersects (b, e)) := by
      rintro X rfl
      conv => lhs; unfold adt.RbT.intersects
      simp only [show ¬ adt.ivlCmp (b, e) z.1 = 0 from hov, ↓reduceIte]
      try rfl
    cases l with
    | leaf =>
      icases adt.ownNode_leaf_open _ _ _ _ $$ Hnl with %Hlp
      subst Hlp
      simp only [_root_.decide_true, Bool.not_true]
      wp_auto
      wp_for_post
      iframe
      iexists rp, x, r
      iframe
      isplitl [Hpack Hiv Hmx Hl Hr' Hp Hc' Hw]
      · iintro Hnr
        iapply Hw
        iapply Hpack $$ [Hiv Hmx Hl Hr' Hp Hc'] [] Hnr
        · iframe
        · iapply adt.ownNode_leaf_close
      ipureintro
      refine ⟨hsr, ?_⟩
      rw [hnode _ rfl]; rfl
    | node cl ll lz lr =>
      icases adt.ownNode_node_open _ _ _ _ cl ll lz lr $$ Hnl with
        ⟨%llp, %lrp, %Hln, Hliv, Hlmx, Hll, Hlr, Hlpp, Hlc, Hlnl, Hlnr⟩
      simp only [Hln.1, decide_false, Bool.not_false]
      wp_auto
      unfold adt.maxW
      wp_apply h_StringAffineComparable_Compare
      ihave Hnl : adt.ownNode tv.sentinel' q x lp (.node cl ll lz lr) $$
          [Hliv Hlmx Hll Hlr Hlpp Hlc Hlnl Hlnr]
      · iapply adt.ownNode_node_close
        iexists llp, lrp
        iframe
        ipureintro; exact Hln
      wp_if_destruct
      · -- left
        simp only [hz, h0] at Hif
        wp_for_post
        iframe
        iexists lp, x, .node cl ll lz lr
        iframe
        isplitl [Hpack Hiv Hmx Hl Hr' Hp Hc' Hw Hnr]
        · iintro Hnl
          iapply Hw
          iapply Hpack $$ [Hiv Hmx Hl Hr' Hp Hc'] Hnl Hnr
          iframe
        ipureintro
        refine ⟨hsl, ?_⟩
        rw [hnode _ rfl]
        simp only [adt.maxEnd_node, show adt.affCmp (adt.nodeMax ll lz lr) b > 0 by omega,
          ↓reduceIte]
      · -- right
        simp only [hz, h0] at Hif
        wp_for_post
        iframe
        iexists rp, x, r
        iframe
        isplitl [Hpack Hiv Hmx Hl Hr' Hp Hc' Hw Hnl]
        · iintro Hnr
          iapply Hw
          iapply Hpack $$ [Hiv Hmx Hl Hr' Hp Hc'] Hnl Hnr
          iframe
        ipureintro
        refine ⟨hsr, ?_⟩
        rw [hnode _ rfl]
        simp only [adt.maxEnd_node, show ¬ adt.affCmp (adt.nodeMax ll lz lr) b > 0 by omega,
          ↓reduceIte]

end proof

end EtcdGrove
end Perennial
