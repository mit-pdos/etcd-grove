module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__replaceParent
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalNode__updateMax

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

theorem adt.intervalTree.replaceParent.wp_proof
    (h_updateMax : adt.intervalNode.updateMax.spec (GF := GF) (hG := hG)) :
    adt.intervalTree.replaceParent.spec (GF := GF) (hG := hG) := by
  intro t s dq C ls x p y yp mh my hxs hys
  wp_start as ⟨Hs, HC, Hxp, Hyp, Hym⟩
  wp_auto
  ihave %Hpar := adt.ownCtxAt_parent _ _ _ _ _ _ _ $$ HC
  cases C with
  | top =>
    have hp : p = s := Hpar.1 rfl
    subst hp
    cases ls with
    | cons f ls => iexfalso; iapply adt.ownCtxAt_top_cons $$ HC
    | nil =>
    icases (adt.ownCtxAt_top _ _ _ _ _).1 $$ HC with ⟨-, Hroot⟩
    rw [_root_.decide_eq_true rfl]
    wp_auto
    iapply HΦ
    ihave HC := (adt.ownCtxAt_top t p y p (some my)).2 $$ [Hroot]
    · iframe; ipureintro; rfl
    iframe
  | inL c C' e r =>
    have hp : p ≠ s := fun h => by have := Hpar.2 h; cases this
    rw [_root_.decide_eq_false hp]
    cases ls with
    | nil => iexfalso; iapply adt.ownCtxAt_inL_nil $$ HC
    | cons f ls =>
    obtain ⟨pp, rp⟩ := f
    icases (adt.ownCtxAt_inL t s c C' e r pp rp ls x p mh).1 $$ HC with
      ⟨%Hpn, Hpiv, Hpmx, Hpl, Hpr, Hpp, Hpc, Hnr, HC⟩
    wp_auto
    icases adt.ownNode_childMax _ _ _ r $$ Hnr with ⟨Hrm, Hrback⟩
    wp_apply h_updateMax t s C' ls p pp y rp e (adt.nodeMaxO mh e r.maxEnd) (some my) r.maxEnd hp
      $$ [HC Hpiv Hpmx Hpl Hpr Hpp Hym Hrm] as ⟨HC, Hpiv, Hpmx, Hpl, Hpr, Hpp, Hym, Hrm⟩
    · rw [adt.childMax_some]; iframe; ipureintro; exact hys
    rw [adt.childMax_some]
    icases Hym with ⟨-, Hym⟩
    ihave Hnr := Hrback $$ Hrm
    iapply HΦ
    iframe
    iapply (adt.ownCtxAt_inL t s c C' e r pp rp ls y p (some my)).2
    iframe
    ipureintro; exact Hpn
  | inR c l e C' =>
    have hp : p ≠ s := fun h => by have := Hpar.2 h; cases this
    rw [_root_.decide_eq_false hp]
    cases ls with
    | nil => iexfalso; iapply adt.ownCtxAt_inR_nil $$ HC
    | cons f ls =>
    obtain ⟨pp, lp⟩ := f
    icases (adt.ownCtxAt_inR t s c l e C' pp lp ls x p mh).1 $$ HC with
      ⟨%Hpn, Hpiv, Hpmx, Hpl, Hpr, Hpp, Hpc, Hnl, HC⟩
    ihave %Hne := adt.ownNode_ne _ _ _ _ _ _ hxs $$ Hnl Hxp
    wp_auto
    rw [_root_.decide_eq_false (Ne.symm Hne)]
    wp_auto
    icases adt.ownNode_childMax _ _ _ l $$ Hnl with ⟨Hlm, Hlback⟩
    wp_apply h_updateMax t s C' ls p pp lp y e (adt.nodeMaxO l.maxEnd e mh) l.maxEnd (some my) hp
      $$ [HC Hpiv Hpmx Hpl Hpr Hpp Hym Hlm] as ⟨HC, Hpiv, Hpmx, Hpl, Hpr, Hpp, Hlm, Hym⟩
    · rw [adt.childMax_some]; iframe; ipureintro; exact hys
    rw [adt.childMax_some]
    icases Hym with ⟨-, Hym⟩
    ihave Hnl := Hlback $$ Hlm
    iapply HΦ
    iframe
    iapply (adt.ownCtxAt_inR t s c l e C' pp lp ls y p (some my)).2
    iframe
    ipureintro; exact Hpn

end proof

end EtcdGrove
end Perennial
