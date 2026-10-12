module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__find
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

theorem adt.intervalTree.find.wp_proof
    (h_StringAffineComparable_Compare :
      adt.StringAffineComparable.Compare.spec (GF := GF) (hG := hG)) :
    adt.intervalTree.find.spec (GF := GF) (hG := hG) := by
  intro t tv q T b e
  wp_start as ⟨Hr, Hs, Hn⟩
  wp_auto
  ihave HI : (∃ (x p : Loc) (Tx : adt.RbT adt.Entry),
      "x" ∷ x_ptr ↦ x ∗ "Hx" ∷ adt.ownNode tv.sentinel' q p x Tx ∗
      "Hw" ∷ (adt.ownNode tv.sentinel' q p x Tx -∗
        adt.ownNode tv.sentinel' q tv.sentinel' tv.root' T) ∗
      "%Hinv" ∷ ⌜Tx.findE (b, e) = T.findE (b, e)⌝ : IProp GF)
      $$ [x Hn]
  · iexists tv.root', tv.sentinel', T
    iframe
    isplitl []
    · iintro H; iexact H
    ipureintro; rfl
  wp_for HI
  cases Tx with
  | leaf =>
    rw [adt.ownNode_leaf]
    icases Hx with %Hx
    subst Hx
    have hvb : decide ((#false : val) = #true) = false :=
      decide_eq_false (fun h => Bool.false_ne_true (go.intoVal_inj h))
    simp only [decide_true, Bool.not_true, hvb, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    iapply HΦ
    iframe Hr Hs
    iexists p, .leaf
    rw [adt.ownNode_leaf]
    isplitl []
    · ipureintro; rfl
    isplitl [Hw]
    · iintro -; iapply Hw; ipureintro; trivial
    ipureintro
    rw [← Hinv]; rfl
  | node c l z r =>
    icases adt.ownNode_node_open _ _ _ _ c l z r $$ Hx with
      ⟨%lp, %rp, %Hn, Hiv, Hmx, Hl, Hr', Hp, Hc, Hnl, Hnr⟩
    simp only [decide_false, Hn.1, Bool.not_false, decide_true, ↓reduceIte]
    icases adt.iv_open _ _ _ _ _ $$ Hiv with ⟨Hb, He, Hv, Hivb⟩
    wp_auto
    wp_apply h_StringAffineComparable_Compare
    wp_apply h_StringAffineComparable_Compare
    have hz : ∀ a c, sint.Z (W64 (adt.affCmp a c)) = adt.affCmp a c := by
      intro a c; have := adt.affCmp_bounds a c; word
    have hw0 : ∀ a c, W64 (adt.affCmp a c) = W64 0 ↔ adt.affCmp a c = 0 := by
      intro a c; have := adt.affCmp_bounds a c; constructor <;> intro h <;> word
    have h0 : sint.Z (W64 0) = 0 := rfl
    have hfe := Hinv
    -- the node, repacked
    ihave Hpack : (x.[intervalNode, go!"iv"].[IntervalValue, go!"Ivl"].[Interval, go!"Begin"] ↦{DFrac.own q}
          interface.mkOk StringAffineComparable.ty #z.1.1 ∗
        x.[intervalNode, go!"iv"].[IntervalValue, go!"Ivl"].[Interval, go!"End"] ↦{DFrac.own q}
          interface.mkOk StringAffineComparable.ty #z.1.2 ∗
        x.[intervalNode, go!"iv"].[IntervalValue, go!"Val"] ↦{DFrac.own q} z.2 ∗
        x.[intervalNode, go!"max"] ↦{DFrac.own q} adt.maxW (adt.nodeMax l z r) ∗
        x.[intervalNode, go!"left"] ↦{DFrac.own q} lp ∗
        x.[intervalNode, go!"right"] ↦{DFrac.own q} rp ∗
        x.[intervalNode, go!"parent"] ↦{DFrac.own q} p ∗
        x.[intervalNode, go!"c"] ↦{DFrac.own q} adt.colorW c -∗
        adt.ownNode tv.sentinel' q x lp l -∗ adt.ownNode tv.sentinel' q x rp r -∗
        adt.ownNode tv.sentinel' q p x (.node c l z r)) $$ [Hivb]
    · iintro ⟨Hb, He, Hv, Hmx, Hl, Hr', Hp, Hc⟩ Hnl Hnr
      iapply adt.ownNode_node_close
      iexists lp, rp
      iframe Hmx Hl Hr' Hp Hc Hnl Hnr
      isplitl []
      · ipureintro; exact Hn
      iapply Hivb; iframe
    -- the descent's three outcomes
    have hcases : ∀ X : Option adt.Entry, X = T.findE (b, e) →
        (adt.affCmp b z.1.1 = 0 ∧ adt.affCmp e z.1.2 = 0 → X = some z) ∧
        (adt.affCmp b z.1.1 < 0 ∨ (adt.affCmp b z.1.1 = 0 ∧ adt.affCmp e z.1.2 < 0) →
          X = l.findE (b, e)) ∧
        (adt.affCmp b z.1.1 > 0 ∨ (adt.affCmp b z.1.1 = 0 ∧ adt.affCmp e z.1.2 > 0) →
          X = r.findE (b, e)) := by
      intro X hX
      rw [hX, ← hfe]
      simp only [adt.RbT.findE]
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
        (split <;> (try split) <;> (try split) <;> (try split)) <;>
        first | rfl | (exfalso; omega)
    have hfound : adt.affCmp b z.1.1 = 0 → adt.affCmp e z.1.2 = 0 →
        T.findE (b, e) = some z := by
      intro h1 h2
      exact (hcases _ rfl).1 ⟨h1, h2⟩
    have hleft : (adt.affCmp b z.1.1 < 0 ∨ (adt.affCmp b z.1.1 = 0 ∧ adt.affCmp e z.1.2 < 0)) →
        l.findE (b, e) = T.findE (b, e) := fun h => ((hcases _ rfl).2.1 h).symm
    have hright : (adt.affCmp b z.1.1 > 0 ∨ (adt.affCmp b z.1.1 = 0 ∧ adt.affCmp e z.1.2 > 0)) →
        r.findE (b, e) = T.findE (b, e) := fun h => ((hcases _ rfl).2.2 h).symm
    wp_if_destruct
    · -- begin equal
      have hb0 := (hw0 _ _).1 Hif
      wp_if_destruct
      · -- found
        have he0 := (hw0 _ _).1 Hif
        wp_for_post
        iapply HΦ
        iframe Hr Hs
        iexists p, .node c l z r
        isplitl [Hpack Hb He Hv Hmx Hl Hr' Hp Hc Hnl Hnr]
        · iapply Hpack $$ [Hb He Hv Hmx Hl Hr' Hp Hc] Hnl Hnr; iframe
        isplitl [Hw]
        · iexact Hw
        ipureintro
        rw [hfound hb0 he0]
        exact ⟨c, l, r, rfl⟩
      · have he0 : adt.affCmp e z.1.2 ≠ 0 := fun h => Hif ((hw0 _ _).2 h)
        wp_if_destruct
        · exfalso; simp only [hz, h0] at Hif; omega
        wp_if_destruct
        · wp_if_destruct
          · -- left
            simp only [hz, h0] at Hif
            wp_for_post
            iframe
            iexists lp, x, l
            iframe
            isplitl [Hpack Hb He Hv Hmx Hl Hr' Hp Hc Hnr Hw]
            · iintro Hnl
              iapply Hw
              iapply Hpack $$ [Hb He Hv Hmx Hl Hr' Hp Hc] Hnl Hnr; iframe
            ipureintro; exact (hleft (Or.inr ⟨hb0, Hif⟩))
          · -- right
            simp only [hz, h0] at Hif
            wp_for_post
            iframe
            iexists rp, x, r
            iframe
            isplitl [Hpack Hb He Hv Hmx Hl Hr' Hp Hc Hnl Hw]
            · iintro Hnr
              iapply Hw
              iapply Hpack $$ [Hb He Hv Hmx Hl Hr' Hp Hc] Hnl Hnr; iframe
            ipureintro; exact (hright (Or.inr ⟨hb0, by omega⟩))
        · exfalso; first | exact Hif ((hw0 _ _).2 hb0) | (simp only [hz, h0] at Hif; omega)
    · have hb0 : adt.affCmp b z.1.1 ≠ 0 := fun h => Hif ((hw0 _ _).2 h)
      wp_if_destruct
      · -- left
        simp only [hz, h0] at Hif
        wp_for_post
        iframe
        iexists lp, x, l
        iframe
        isplitl [Hpack Hb He Hv Hmx Hl Hr' Hp Hc Hnr Hw]
        · iintro Hnl
          iapply Hw
          iapply Hpack $$ [Hb He Hv Hmx Hl Hr' Hp Hc] Hnl Hnr; iframe
        ipureintro; exact (hleft (Or.inl Hif))
      · simp only [hz, h0] at Hif
        wp_if_destruct
        · exfalso; exact hb0 ((hw0 _ _).1 Hif)
        -- right
        wp_for_post
        iframe
        iexists rp, x, r
        iframe
        isplitl [Hpack Hb He Hv Hmx Hl Hr' Hp Hc Hnl Hw]
        · iintro Hnr
          iapply Hw
          iapply Hpack $$ [Hb He Hv Hmx Hl Hr' Hp Hc] Hnl Hnr; iframe
        ipureintro; exact (hright (Or.inl (by omega)))

end proof

end EtcdGrove
end Perennial
