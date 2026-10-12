module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalNode__updateMax
public import Spec.go_etcd_io.etcd.pkg.v3.adt.StringAffineComparable__Compare

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

theorem adt.intervalNode.updateMax.wp_proof
    (h_StringAffineComparable_Compare :
      adt.StringAffineComparable.Compare.spec (GF := GF) (hG := hG)) :
    adt.intervalNode.updateMax.spec (GF := GF) (hG := hG) := by
  intro t s C x p lp rp e m0 ml mr hxs
  wp_start as ⟨HC, Hiv, Hmx, Hl, Hr, Hp, Hml, Hmr⟩
  wp_auto
  ihave HI : (∃ y : Loc, "x" ∷ x_ptr ↦ y ∗ "HJ" ∷
      ((⌜y = s⌝ ∗ (adt.ownCtx t s C x p (some (adt.nodeMaxO ml e mr)) ∗
        x.[intervalNode, go!"iv"] ↦
          ({ Ivl' := adt.affIvl e.1.1 e.1.2, Val' := e.2 } : IntervalValue) ∗
        x.[intervalNode, go!"max"] ↦ adt.maxW (adt.nodeMaxO ml e mr) ∗
        x.[intervalNode, go!"left"] ↦ lp ∗ x.[intervalNode, go!"right"] ↦ rp ∗
        x.[intervalNode, go!"parent"] ↦ p ∗
        adt.childMax s lp ml ∗ adt.childMax s rp mr)) ∨
      (∃ (C' : adt.RbCtx adt.Entry) (p' lp' rp' : Loc) (e' : adt.Entry) (m0' : GoString)
          (ml' mr' : Option GoString),
        ⌜y ≠ s⌝ ∗ adt.ownCtx t s C' y p' (some m0') ∗
        y.[intervalNode, go!"iv"] ↦
          ({ Ivl' := adt.affIvl e'.1.1 e'.1.2, Val' := e'.2 } : IntervalValue) ∗
        y.[intervalNode, go!"max"] ↦ adt.maxW m0' ∗
        y.[intervalNode, go!"left"] ↦ lp' ∗ y.[intervalNode, go!"right"] ↦ rp' ∗
        y.[intervalNode, go!"parent"] ↦ p' ∗
        adt.childMax s lp' ml' ∗ adt.childMax s rp' mr' ∗
        (adt.ownCtx t s C' y p' (some (adt.nodeMaxO ml' e' mr')) ∗
          y.[intervalNode, go!"iv"] ↦
            ({ Ivl' := adt.affIvl e'.1.1 e'.1.2, Val' := e'.2 } : IntervalValue) ∗
          y.[intervalNode, go!"max"] ↦ adt.maxW (adt.nodeMaxO ml' e' mr') ∗
          y.[intervalNode, go!"left"] ↦ lp' ∗ y.[intervalNode, go!"right"] ↦ rp' ∗
          y.[intervalNode, go!"parent"] ↦ p' ∗
          adt.childMax s lp' ml' ∗ adt.childMax s rp' mr' -∗
          (adt.ownCtx t s C x p (some (adt.nodeMaxO ml e mr)) ∗
            x.[intervalNode, go!"iv"] ↦
              ({ Ivl' := adt.affIvl e.1.1 e.1.2, Val' := e.2 } : IntervalValue) ∗
            x.[intervalNode, go!"max"] ↦ adt.maxW (adt.nodeMaxO ml e mr) ∗
            x.[intervalNode, go!"left"] ↦ lp ∗ x.[intervalNode, go!"right"] ↦ rp ∗
            x.[intervalNode, go!"parent"] ↦ p ∗
            adt.childMax s lp ml ∗ adt.childMax s rp mr)))) : IProp GF)
      $$ [x HC Hiv Hmx Hl Hr Hp Hml Hmr]
  · iexists x
    iframe x
    iright
    iexists C, p, lp, rp, e, m0, ml, mr
    iframe
    isplitl []
    · ipureintro; exact hxs
    iintro H; iexact H
  wp_for HI
  have hvb : decide ((#false : val) = #true) = false :=
    decide_eq_false (fun h => Bool.false_ne_true (go.intoVal_inj h))
  have hvt : decide ((#true : val) = #true) = true := decide_eq_true rfl
  icases HJ with (⟨%Hy, HR⟩ | ⟨%C', %p', %lp', %rp', %e', %m0', %ml', %mr', %Hy, HC, Hiv, Hmx,
    Hl, Hr, Hp, Hml, Hmr, Hw⟩)
  · rw [Hy]
    simp only [decide_true, Bool.not_true, hvb, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    iapply HΦ; iexact HR
  simp only [decide_false, Hy, Bool.not_false, _root_.decide_true, ↓reduceIte]
  icases adt.iv_open _ _ _ _ _ $$ Hiv with ⟨Hb, He, Hv, Hivb⟩
  wp_auto
  have hz : ∀ a c, sint.Z (W64 (adt.affCmp a c)) = adt.affCmp a c := by
    intro a c; have := adt.affCmp_bounds a c; word
  have h0 : sint.Z (W64 0) = 0 := rfl
  have hmax_gt : ∀ a b, sint.Z (W64 0) < sint.Z (W64 (adt.affCmp b a)) →
      adt.affMaxO a (some b) = b := by
    intro a b h; rw [hz, h0] at h; simp [adt.affMaxO, show adt.affCmp b a > 0 by omega]
  have hmax_le : ∀ a b, ¬ sint.Z (W64 0) < sint.Z (W64 (adt.affCmp b a)) →
      adt.affMaxO a (some b) = a := by
    intro a b h; rw [hz, h0] at h; simp [adt.affMaxO, show ¬ adt.affCmp b a > 0 by omega]
  -- the left child's max
  wp_join iprop(max_ptr ↦ interface.mkOk StringAffineComparable.ty #(adt.affMaxO e'.1.2 ml') ∗
      adt.childMax s lp' ml' ∗ x_ptr ↦ y ∗ y.[intervalNode, go!"left"] ↦ lp')
    with [max Hml x Hl] as ⟨max, Hml, x, Hl⟩
  · cases ml' with
    | none =>
      rw [adt.childMax_none]
      simp only [adt.affMaxO]
      iframe
    | some m =>
      rw [adt.childMax_some]
      icases Hml with ⟨%Hlp, -⟩
      exact absurd Hif Hlp
  · cases ml' with
    | none =>
      rw [adt.childMax_none]
      icases Hml with %Hlp
      exact absurd Hlp Hif
    | some m =>
      rw [adt.childMax_some]
      icases Hml with ⟨%Hlp, Hlm⟩
      wp_auto
      unfold adt.maxW
      wp_apply h_StringAffineComparable_Compare
      wp_if_destruct
      · rw [hmax_gt _ _ Hif]
        iframe; ipureintro; exact Hlp
      · rw [hmax_le _ _ Hif]
        iframe; ipureintro; exact Hlp
  -- the right child's max
  wp_join iprop(max_ptr ↦ interface.mkOk StringAffineComparable.ty
        #(adt.affMaxO (adt.affMaxO e'.1.2 ml') mr') ∗
      adt.childMax s rp' mr' ∗ x_ptr ↦ y ∗ y.[intervalNode, go!"right"] ↦ rp')
    with [max Hmr x Hr] as ⟨max, Hmr, x, Hr⟩
  · cases mr' with
    | none =>
      rw [adt.childMax_none]
      simp only [adt.affMaxO]
      iframe
    | some m =>
      rw [adt.childMax_some]
      icases Hmr with ⟨%Hrp, -⟩
      exact absurd Hif Hrp
  · cases mr' with
    | none =>
      rw [adt.childMax_none]
      icases Hmr with %Hrp
      exact absurd Hrp Hif
    | some m =>
      rw [adt.childMax_some]
      icases Hmr with ⟨%Hrp, Hrm⟩
      wp_auto
      unfold adt.maxW
      wp_apply h_StringAffineComparable_Compare
      wp_if_destruct
      · rw [hmax_gt _ _ Hif]
        iframe; ipureintro; exact Hrp
      · rw [hmax_le _ _ Hif]
        iframe; ipureintro; exact Hrp
  -- unchanged: stop
  unfold adt.maxW
  wp_apply h_StringAffineComparable_Compare
  ihave Hiv := Hivb $$ [Hb He Hv]
  · iframe
  wp_if_destruct
  · -- unchanged: the nodes above are right
    have heq : m0' = adt.affMaxO (adt.affMaxO e'.1.2 ml') mr' := by
      have := adt.affCmp_bounds m0' (adt.affMaxO (adt.affMaxO e'.1.2 ml') mr')
      exact (adt.affCmp_eq_zero_iff _ _).1 (by word)
    wp_for_post
    iapply HΦ
    iapply Hw
    rw [heq]
    iframe
  · wp_for_post
    iframe HΦ sentinel
    iexists p'
    iframe x
    ihave %Hpar := adt.ownCtx_parent _ _ _ _ _ _ $$ HC
    cases C' with
    | top =>
      ileft
      isplitl []
      · ipureintro; exact Hpar.1 rfl
      iapply Hw
      ihave HC := adt.ownCtx_top_any _ _ _ _ _ (some (adt.nodeMaxO ml' e' mr')) $$ HC
      unfold adt.nodeMaxO
      iframe
    | inL c C'' pe r =>
      rw [adt.ownCtx_inL]
      icases HC with ⟨%pp, %rp2, %Hpn, Hpiv, Hpmx, Hpl, Hpr, Hpp, Hpc, Hnr, HC⟩
      icases adt.ownNode_childMax _ _ _ r $$ Hnr with ⟨Hrm, Hrback⟩
      iright
      iexists C'', pp, y, rp2, pe, adt.nodeMaxO (some m0') pe r.maxEnd,
        some (adt.nodeMaxO ml' e' mr'), r.maxEnd
      simp only [adt.maxW, adt.childMax_some]
      iframe HC Hpiv Hpmx Hpl Hpr Hpp Hrm
      isplitl []
      · ipureintro; exact Hpn.1
      isplitl [Hmx]
      · iframe; ipureintro; exact Hy
      iintro ⟨HC, Hpiv, Hpmx, Hpl, Hpr, Hpp, ⟨-, Hmx⟩, Hrm⟩
      ihave Hnr := Hrback $$ Hrm
      iapply Hw
      rw [adt.ownCtx_inL]
      simp only [adt.maxW]
      unfold adt.nodeMaxO
      iframe
      ipureintro; exact Hpn
    | inR c l pe C'' =>
      rw [adt.ownCtx_inR]
      icases HC with ⟨%pp, %lp2, %Hpn, Hpiv, Hpmx, Hpl, Hpr, Hpp, Hpc, Hnl, HC⟩
      icases adt.ownNode_childMax _ _ _ l $$ Hnl with ⟨Hlm, Hlback⟩
      iright
      iexists C'', pp, lp2, y, pe, adt.nodeMaxO l.maxEnd pe (some m0'), l.maxEnd,
        some (adt.nodeMaxO ml' e' mr')
      simp only [adt.maxW, adt.childMax_some]
      iframe HC Hpiv Hpmx Hpl Hpr Hpp Hlm
      isplitl []
      · ipureintro; exact Hpn.1
      isplitl [Hmx]
      · iframe; ipureintro; exact Hy
      iintro ⟨HC, Hpiv, Hpmx, Hpl, Hpr, Hpp, Hlm, ⟨-, Hmx⟩⟩
      ihave Hnl := Hlback $$ Hlm
      iapply Hw
      rw [adt.ownCtx_inR]
      simp only [adt.maxW]
      unfold adt.nodeMaxO
      iframe
      ipureintro; exact Hpn

end proof

end EtcdGrove
end Perennial
