/-
`intervalTree.Intersects` (`interval_tree.go`) over a comparator: the proof of
`Spec/.../adt/intervalTree__Intersects_gen.lean` (unit 4, generalized in the auth plan's S2b). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Intersects_gen
public import Spec.go_etcd_io.etcd.pkg.v3.adt.Interval__Compare
public import Proof.go_etcd_io.etcd.pkg.v3.adt.NodeLemmas

@[expose] public section

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

theorem adt.intervalTree.Intersects_gen.wp_proof
    (h_Interval_Compare : adt.Interval.Compare.spec (GF := GF) (hG := hG)) :
    adt.intervalTree.Intersects_gen.spec (GF := GF) (hG := hG) := by
  intro K hK t L vb ve db de b e q
  wp_start as ⟨Ht, Hkb, Hke⟩
  icases adt.ownIvtK_read K _ _ _ $$ Ht with ⟨%tv, %T, Hr, Hc, Hs, Hn, %Hp, Hback⟩
  obtain ⟨hTL, -, hsorted, -⟩ := Hp
  subst hTL
  wp_auto
  ihave HI : (∃ (x p : Loc) (Tx : adt.RbT adt.Entry),
      "x" ∷ x_ptr ↦ x ∗ "Hx" ∷ adt.ownNode K tv.sentinel' q p x Tx ∗
      "Hw" ∷ (adt.ownNode K tv.sentinel' q p x Tx -∗
        adt.ownNode K tv.sentinel' q tv.sentinel' tv.root' T) ∗
      "Hkb" ∷ K.keyAt db vb b ∗ "Hke" ∷ K.keyAt de ve e ∗
      "%Hinv" ∷ ⌜adt.IvSorted Tx.inorder ∧ Tx.intersects (b, e) = T.intersects (b, e)⌝ : IProp GF)
      $$ [x Hn Hkb Hke]
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
    icases adt.ownNode_leaf_open K _ _ _ _ $$ Hx with %Hx
    subst Hx
    simp only [decide_true, Bool.not_true]
    simp only [adt.RbT.intersects]
    wp_auto
    simp only [hvf, Bool.false_eq_true, _root_.decide_true, ↓reduceIte]
    wp_auto
    iapply HΦ
    iframe Hkb Hke
    iapply Hback
    iframe
    iapply Hw
    iapply adt.ownNode_leaf_close
  | node c l z r =>
    icases adt.ownNode_node_open K _ _ _ _ c l z r $$ Hx with
      ⟨%lp, %rp, %Hn, Hiv, Hmx, Hl, Hr', Hp, Hc', Hnl, Hnr⟩
    simp only [decide_false, Hn.1, Bool.not_false]
    icases K.ivAt_open_ivl _ _ _ $$ Hiv with ⟨%zb, %ze, Hivl, #Hkzb, #Hkze, Hivb⟩
    wp_auto
    wp_apply (h_Interval_Compare K hK) iv_ptr (DFrac.own 1) vb ve db de b e _ q zb ze
      .discard .discard z.1.1 z.1.2 $$ [iv Hkb Hke Hivl] as ⟨iv, Hkb, Hke, Hivl, -, -⟩
    · iframe ∗ #
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
    ihave Hpack : (K.ivAt x.[intervalNode, go!"iv"] q z ∗
        K.maxAt x.[intervalNode, go!"max"] q (adt.nodeMax l z r) ∗
        x.[intervalNode, go!"left"] ↦{q} lp ∗
        x.[intervalNode, go!"right"] ↦{q} rp ∗
        x.[intervalNode, go!"parent"] ↦{q} p ∗
        x.[intervalNode, go!"c"] ↦{q} adt.colorW c -∗
        adt.ownNode K tv.sentinel' q x lp l -∗ adt.ownNode K tv.sentinel' q x rp r -∗
        adt.ownNode K tv.sentinel' q p x (.node c l z r)) $$ []
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
      iframe Hkb Hke
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
      icases adt.ownNode_leaf_open K _ _ _ _ $$ Hnl with %Hlp
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
      icases adt.ownNode_node_open K _ _ _ _ cl ll lz lr $$ Hnl with
        ⟨%llp, %lrp, %Hln, Hliv, Hlmx, Hll, Hlr, Hlpp, Hlc, Hlnl, Hlnr⟩
      simp only [Hln.1, decide_false, Bool.not_false]
      icases K.maxAt_open _ _ _ $$ Hlmx with ⟨%vlm, Hlmx, #Hklm⟩
      icases K.ivAt_open _ _ _ $$ Hiv with ⟨%zb', %ze', Hb, He, Hv, -, -, Hivb⟩
      wp_auto
      wp_apply hK .discard db vlm vb (adt.nodeMax ll lz lr) b $$ [Hkb] as ⟨-, Hkb⟩
      · iframe ∗ #
      ihave Hiv := Hivb $$ [Hb He Hv]
      · iframe
      ihave Hlmx := K.maxAt_intro _ _ _ vlm $$ [Hlmx]
      · iframe ∗ #
      ihave Hnl : adt.ownNode K tv.sentinel' q x lp (.node cl ll lz lr) $$
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
