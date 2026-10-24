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

theorem adt.intervalNode.updateMax.wp_proof :
    adt.intervalNode.updateMax.spec (GF := GF) (hG := hG) := by
  intro K hK t s C ls x p lp rp e m0 ml mr hxs
  wp_start as ⟨HC, Hiv, Hmx, Hl, Hr, Hp, Hml, Hmr⟩
  wp_auto
  ihave HI : (∃ y : Loc, "x" ∷ x_ptr ↦ y ∗ "HJ" ∷
      ((⌜y = s⌝ ∗ (adt.ownCtxAt K t s C ls x p (some (adt.nodeMaxO ml e mr)) ∗
        K.ivAt x.[intervalNode, go!"iv"] (DFrac.own 1) e ∗
        K.maxAt x.[intervalNode, go!"max"] (DFrac.own 1) (adt.nodeMaxO ml e mr) ∗
        x.[intervalNode, go!"left"] ↦ lp ∗ x.[intervalNode, go!"right"] ↦ rp ∗
        x.[intervalNode, go!"parent"] ↦ p ∗
        adt.childMax K s lp ml ∗ adt.childMax K s rp mr)) ∨
      (∃ (C' : adt.RbCtx adt.Entry) (ls' : List (Loc × Loc)) (p' lp' rp' : Loc) (e' : adt.Entry)
          (m0' : GoString) (ml' mr' : Option GoString),
        ⌜y ≠ s⌝ ∗ adt.ownCtxAt K t s C' ls' y p' (some m0') ∗
        K.ivAt y.[intervalNode, go!"iv"] (DFrac.own 1) e' ∗
        K.maxAt y.[intervalNode, go!"max"] (DFrac.own 1) m0' ∗
        y.[intervalNode, go!"left"] ↦ lp' ∗ y.[intervalNode, go!"right"] ↦ rp' ∗
        y.[intervalNode, go!"parent"] ↦ p' ∗
        adt.childMax K s lp' ml' ∗ adt.childMax K s rp' mr' ∗
        (adt.ownCtxAt K t s C' ls' y p' (some (adt.nodeMaxO ml' e' mr')) ∗
          K.ivAt y.[intervalNode, go!"iv"] (DFrac.own 1) e' ∗
          K.maxAt y.[intervalNode, go!"max"] (DFrac.own 1) (adt.nodeMaxO ml' e' mr') ∗
          y.[intervalNode, go!"left"] ↦ lp' ∗ y.[intervalNode, go!"right"] ↦ rp' ∗
          y.[intervalNode, go!"parent"] ↦ p' ∗
          adt.childMax K s lp' ml' ∗ adt.childMax K s rp' mr' -∗
          (adt.ownCtxAt K t s C ls x p (some (adt.nodeMaxO ml e mr)) ∗
            K.ivAt x.[intervalNode, go!"iv"] (DFrac.own 1) e ∗
            K.maxAt x.[intervalNode, go!"max"] (DFrac.own 1) (adt.nodeMaxO ml e mr) ∗
            x.[intervalNode, go!"left"] ↦ lp ∗ x.[intervalNode, go!"right"] ↦ rp ∗
            x.[intervalNode, go!"parent"] ↦ p ∗
            adt.childMax K s lp ml ∗ adt.childMax K s rp mr)))) : IProp GF)
      $$ [x HC Hiv Hmx Hl Hr Hp Hml Hmr]
  · iexists x
    iframe x
    iright
    iexists C, ls, p, lp, rp, e, m0, ml, mr
    iframe
    isplitl []
    · ipureintro; exact hxs
    iintro H; iexact H
  wp_for HI
  have hvb : decide ((#false : val) = #true) = false :=
    decide_eq_false (fun h => Bool.false_ne_true (go.intoVal_inj h))
  have hvt : decide ((#true : val) = #true) = true := decide_eq_true rfl
  icases HJ with (⟨%Hy, HR⟩ | ⟨%C', %ls', %p', %lp', %rp', %e', %m0', %ml', %mr', %Hy, HC, Hiv, Hmx,
    Hl, Hr, Hp, Hml, Hmr, Hw⟩)
  · rw [Hy]
    simp only [decide_true, Bool.not_true, hvb, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    iapply HΦ; iexact HR
  simp only [decide_false, Hy, Bool.not_false, _root_.decide_true, ↓reduceIte]
  icases K.ivAt_open _ _ _ $$ Hiv with ⟨%vb', %ve', Hb, He, Hv, #Hkb', #Hke', Hivb⟩
  icases K.maxAt_open _ _ _ $$ Hmx with ⟨%vm0, Hmx, #Hkm0⟩
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
  wp_join iprop(∃ vmax : val, max_ptr ↦ interface.mkOk K.ty vmax ∗
      K.keyAt .discard vmax (adt.affMaxO e'.1.2 ml') ∗
      adt.childMax K s lp' ml' ∗ x_ptr ↦ y ∗ y.[intervalNode, go!"left"] ↦ lp')
    with [max Hml x Hl] as ⟨%vmax, max, #Hkmax, Hml, x, Hl⟩
  · cases ml' with
    | none =>
      rw [adt.childMax_none]
      simp only [adt.affMaxO]
      iexists ve'
      iframe ∗ #
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
      icases K.maxAt_open _ _ _ $$ Hlm with ⟨%vlm, Hlm, #Hklm⟩
      wp_auto
      wp_apply hK .discard .discard vlm ve' m e'.1.2 $$ [] as ⟨-, -⟩
      · iframe ∗ #
      wp_if_destruct
      · rw [hmax_gt _ _ Hif]
        ihave Hlm := K.maxAt_intro _ _ _ vlm $$ [Hlm]
        · iframe ∗ #
        isplitl []
        · itrivial
        iexists vlm
        iframe ∗ #
        ipureintro; exact Hlp
      · rw [hmax_le _ _ Hif]
        ihave Hlm := K.maxAt_intro _ _ _ vlm $$ [Hlm]
        · iframe ∗ #
        isplitl []
        · itrivial
        iexists ve'
        iframe ∗ #
        ipureintro; exact Hlp
  -- the right child's max
  wp_join iprop(∃ vmax' : val, max_ptr ↦ interface.mkOk K.ty vmax' ∗
      K.keyAt .discard vmax' (adt.affMaxO (adt.affMaxO e'.1.2 ml') mr') ∗
      adt.childMax K s rp' mr' ∗ x_ptr ↦ y ∗ y.[intervalNode, go!"right"] ↦ rp')
    with [max Hmr x Hr] as ⟨%vmax', max, #Hkmax', Hmr, x, Hr⟩
  · cases mr' with
    | none =>
      rw [adt.childMax_none]
      simp only [adt.affMaxO]
      iexists vmax
      iframe ∗ #
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
      icases K.maxAt_open _ _ _ $$ Hrm with ⟨%vrm, Hrm, #Hkrm⟩
      wp_auto
      wp_apply hK .discard .discard vrm vmax m (adt.affMaxO e'.1.2 ml') $$ [] as ⟨-, -⟩
      · iframe ∗ #
      wp_if_destruct
      · rw [hmax_gt _ _ Hif]
        ihave Hrm := K.maxAt_intro _ _ _ vrm $$ [Hrm]
        · iframe ∗ #
        isplitl []
        · itrivial
        iexists vrm
        iframe ∗ #
        ipureintro; exact Hrp
      · rw [hmax_le _ _ Hif]
        ihave Hrm := K.maxAt_intro _ _ _ vrm $$ [Hrm]
        · iframe ∗ #
        isplitl []
        · itrivial
        iexists vmax
        iframe ∗ #
        ipureintro; exact Hrp
  -- unchanged: stop
  wp_apply hK .discard .discard vm0 vmax' m0' (adt.affMaxO (adt.affMaxO e'.1.2 ml') mr')
    $$ [] as ⟨-, -⟩
  · iframe ∗ #
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
    ihave Hmx := K.maxAt_intro _ _ _ vm0 $$ [Hmx]
    · iframe ∗ #
    unfold adt.nodeMaxO
    rw [heq]
    iframe
  · wp_for_post
    ihave Hmx := K.maxAt_intro _ _ _ vmax' $$ [Hmx]
    · iframe ∗ #
    iframe HΦ sentinel
    iexists p'
    iframe x
    ihave %Hpar := adt.ownCtxAt_parent K _ _ _ _ _ _ _ $$ HC
    cases C' with
    | top =>
      ileft
      isplitl []
      · ipureintro; exact Hpar.1 rfl
      iapply Hw
      ihave HC := adt.ownCtxAt_top_any K _ _ _ _ _ _ (some (adt.nodeMaxO ml' e' mr')) $$ HC
      unfold adt.nodeMaxO
      iframe
    | inL c C'' pe r =>
      cases ls' with
      | nil => iexfalso; iapply adt.ownCtxAt_inL_nil K $$ HC
      | cons f ls'' =>
      obtain ⟨pp, rp2⟩ := f
      icases (adt.ownCtxAt_inL K _ _ _ _ _ _ _ _ _ _ _ _).1 $$ HC with
        ⟨%Hpn, Hpiv, Hpmx, Hpl, Hpr, Hpp, Hpc, Hnr, HC⟩
      icases adt.ownNode_childMax K _ _ _ r $$ Hnr with ⟨Hrm, Hrback⟩
      iright
      iexists C'', ls'', pp, y, rp2, pe, adt.nodeMaxO (some m0') pe r.maxEnd,
        some (adt.nodeMaxO ml' e' mr'), r.maxEnd
      simp only [adt.childMax_some]
      iframe HC Hpiv Hpmx Hpl Hpr Hpp Hrm
      isplitl []
      · ipureintro; exact Hpn.1
      isplitl [Hmx]
      · unfold adt.nodeMaxO; iframe; ipureintro; exact Hy
      iintro ⟨HC, Hpiv, Hpmx, Hpl, Hpr, Hpp, ⟨-, Hmx⟩, Hrm⟩
      ihave Hnr := Hrback $$ Hrm
      iapply Hw
      ihave HC := (adt.ownCtxAt_inL K _ _ _ _ _ _ _ _ _ y p' (some (adt.nodeMaxO ml' e' mr'))).2
        $$ [HC Hpiv Hpmx Hpl Hpr Hpp Hpc Hnr]
      · unfold adt.nodeMaxO
        iframe
        ipureintro; exact Hpn
      unfold adt.nodeMaxO
      iframe
    | inR c l pe C'' =>
      cases ls' with
      | nil => iexfalso; iapply adt.ownCtxAt_inR_nil K $$ HC
      | cons f ls'' =>
      obtain ⟨pp, lp2⟩ := f
      icases (adt.ownCtxAt_inR K _ _ _ _ _ _ _ _ _ _ _ _).1 $$ HC with
        ⟨%Hpn, Hpiv, Hpmx, Hpl, Hpr, Hpp, Hpc, Hnl, HC⟩
      icases adt.ownNode_childMax K _ _ _ l $$ Hnl with ⟨Hlm, Hlback⟩
      iright
      iexists C'', ls'', pp, lp2, y, pe, adt.nodeMaxO l.maxEnd pe (some m0'), l.maxEnd,
        some (adt.nodeMaxO ml' e' mr')
      simp only [adt.childMax_some]
      iframe HC Hpiv Hpmx Hpl Hpr Hpp Hlm
      isplitl []
      · ipureintro; exact Hpn.1
      isplitl [Hmx]
      · unfold adt.nodeMaxO; iframe; ipureintro; exact Hy
      iintro ⟨HC, Hpiv, Hpmx, Hpl, Hpr, Hpp, Hlm, ⟨-, Hmx⟩⟩
      ihave Hnl := Hlback $$ Hlm
      iapply Hw
      ihave HC := (adt.ownCtxAt_inR K _ _ _ _ _ _ _ _ _ y p' (some (adt.nodeMaxO ml' e' mr'))).2
        $$ [HC Hpiv Hpmx Hpl Hpr Hpp Hpc Hnl]
      · unfold adt.nodeMaxO
        iframe
        ipureintro; exact Hpn
      unfold adt.nodeMaxO
      iframe

end proof

end EtcdGrove
end Perennial
