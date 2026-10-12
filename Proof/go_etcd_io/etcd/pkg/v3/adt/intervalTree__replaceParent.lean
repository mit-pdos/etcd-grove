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
  intro t s dq C x p y yp mh my hxs hys
  wp_start as ⟨Hs, HC, Hxp, Hyp, Hym⟩
  wp_auto
  ihave %Hpar := adt.ownCtx_parent _ _ _ _ _ _ $$ HC
  cases C with
  | top =>
    have hp : p = s := Hpar.1 rfl
    subst hp
    rw [adt.ownCtx_top t _ x]
    icases HC with ⟨-, Hroot⟩
    rw [_root_.decide_eq_true rfl]
    wp_auto
    iapply HΦ
    rw [adt.ownCtx_top]
    iframe
    ipureintro <;> rfl
  | inL c C' e r =>
    have hp : p ≠ s := fun h => by have := Hpar.2 h; cases this
    rw [_root_.decide_eq_false hp, adt.ownCtx_inL t s c C' e r x]
    icases HC with ⟨%pp, %rp, %Hpn, Hpiv, Hpmx, Hpl, Hpr, Hpp, Hpc, Hnr, HC⟩
    wp_auto
    icases adt.ownNode_childMax _ _ _ r $$ Hnr with ⟨Hrm, Hrback⟩
    wp_apply h_updateMax t s C' p pp y rp e (adt.nodeMaxO mh e r.maxEnd) (some my) r.maxEnd hp
      $$ [HC Hpiv Hpmx Hpl Hpr Hpp Hym Hrm] as ⟨HC, Hpiv, Hpmx, Hpl, Hpr, Hpp, Hym, Hrm⟩
    · rw [adt.childMax_some]; iframe; ipureintro; exact hys
    rw [adt.childMax_some]
    icases Hym with ⟨-, Hym⟩
    ihave Hnr := Hrback $$ Hrm
    iapply HΦ
    rw [adt.ownCtx_inL]
    iframe
    ipureintro; exact Hpn
  | inR c l e C' =>
    have hp : p ≠ s := fun h => by have := Hpar.2 h; cases this
    rw [_root_.decide_eq_false hp, adt.ownCtx_inR t s c l e C' x]
    icases HC with ⟨%pp, %lp, %Hpn, Hpiv, Hpmx, Hpl, Hpr, Hpp, Hpc, Hnl, HC⟩
    ihave %Hne := adt.ownNode_ne _ _ _ _ _ _ hxs $$ Hnl Hxp
    wp_auto
    rw [_root_.decide_eq_false (Ne.symm Hne)]
    wp_auto
    icases adt.ownNode_childMax _ _ _ l $$ Hnl with ⟨Hlm, Hlback⟩
    wp_apply h_updateMax t s C' p pp lp y e (adt.nodeMaxO l.maxEnd e mh) l.maxEnd (some my) hp
      $$ [HC Hpiv Hpmx Hpl Hpr Hpp Hym Hlm] as ⟨HC, Hpiv, Hpmx, Hpl, Hpr, Hpp, Hlm, Hym⟩
    · rw [adt.childMax_some]; iframe; ipureintro; exact hys
    rw [adt.childMax_some]
    icases Hym with ⟨-, Hym⟩
    ihave Hnl := Hlback $$ Hlm
    iapply HΦ
    rw [adt.ownCtx_inR]
    iframe
    ipureintro; exact Hpn

end proof

end EtcdGrove
end Perennial
