/-
Proof of `Spec/k8s_io/kubernetes/pkg/controller/daemon/DaemonSetsController__updateDaemonSet.lean` over its callees' specs. Lean-first; Stage 3 of the autoverify run
(`notes/k8s-daemonset-run/`, track B): a stub.

A glue proof (Stage 3, step 3).
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__updateDaemonSet
public import Spec.fmt.Errorf
public import Proof.k8s_io.kubernetes.pkg.controller.daemon.DsLens
public import Spec.k8s_io.klog.v2.FromContext
public import Spec.k8s_io.kubernetes.pkg.controller.ControllerExpectations__SatisfiedExpectations
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__cleanupHistory
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__manage
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__rollingUpdate

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode apimodel consistency k8s_io.kubernetes.pkg.controller.daemon

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.daemon.Assumptions]
variable [api_sem : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Assumptions]

theorem DaemonSetsController.updateDaemonSet.wp_proof
    (wp_manage : DaemonSetsController.manage.spec (GF := GF) (hG := hG))
    (wp_rollingUpdate : DaemonSetsController.rollingUpdate.spec (GF := GF) (hG := hG))
    (wp_cleanupHistory : DaemonSetsController.cleanupHistory.spec (GF := GF) (hG := hG))
    (wp_SatisfiedExpectations : ControllerExpectations.SatisfiedExpectations.spec (GF := GF) (hG := hG))
    (wp_FromContext : klog.FromContext.spec (GF := GF) (hG := hG))
    (wp_Errorf : fmt.Errorf.spec (GF := GF) (hG := hG)) :
    DaemonSetsController.updateDaemonSet.spec (GF := GF) (hG := hG) := by
  intro dsc c cfg γa F γ ctx ds o d nl ns hash key old rs L
  wp_start as ⟨#Henv, Htt, %Hctx, #Hds, #Hnl, %Hnd, Hold, Hready⟩
  wp_auto
  wp_apply (wp_manage dsc c cfg γa F γ ctx ds o d nl ns hash L) $$ [Htt Hready]
    as %err ⟨Htt, Hsync, Herr⟩
  · iframe #
    iframe
    isplitr
    · ipureintro; exact Hctx
    · ipureintro; exact Hnd
  cases err with
  | ok ei =>
    wp_auto
    iapply HΦ
    iframe
  | nil =>
  wp_auto
  ihave Henv2 := Henv
  iunfold dscEnv at Henv2
  icases Henv2 with ⟨#Hpkgd, #Hdsc, #Hapi, #Hs1⟩
  iNamed Hdsc
  iunfold dscPools at Hpools
  icases Hpools with ⟨%Htb, #Hpds, #Hpcr, #Hppod, #Hpnode, #Hpexp, #Hpcons⟩
  wp_apply (lc := 1) (wp_FromContext ctx) as %lg _
  · ipureintro; exact Hctx
  iapply fupd_wp
  imod threadPool.borrow_lc (dscPoolN.@"exp") c.pools.exp (expReader c.γe) ⊤
    (fun _ _ => CoPset.mem_full) $$ [Hlc1 Hpexp Htt] with ⟨HR, Hloan⟩
  · iframe #; iframe
  imodintro
  wp_apply (wp_SatisfiedExpectations c.exp c.γe lg key) $$ [HR] as %b HR
  · iframe #; iframe
  iapply fupd_wp
  imod threadPool.giveBack (dscPoolN.@"exp") c.pools.exp (expReader c.γe) ⊤
    (fun _ _ => CoPset.mem_full) $$ [Hpexp Hloan HR] with Htt
  · iframe #; iframe
  imodintro
  ihave HdsU := Hds
  iunfold dsArg at HdsU
  icases HdsU with ⟨#HdsAt, #Hseen⟩
  ihave #Hty := dsAt_updType ds d $$ HdsAt
  wp_if_destruct
  · -- expectations not satisfied
    wp_apply (wp_cleanupHistory dsc c cfg γa F γ ctx ds o d old rs) $$ [Htt Hold]
      as %e2 ⟨Htt, He2, Hold⟩
    · iframe #; iframe; ipureintro; exact Hctx
    cases e2 with
    | nil =>
      wp_auto
      iapply HΦ
      iframe
    | ok ei =>
      wp_auto
      wp_apply wp_slice_literal (V := GoInterface) [interface.ok ei]
      isplitr
      · ipureintro; rfl
      iintro %asl ⟨Hasl, -⟩
      wp_auto
      wp_apply (wp_Errorf _ _ [interface.ok ei] (DFrac.own 1)) $$ [Hasl He2] as %e3 ⟨-, #He3⟩
      · iframe
        iunfold fmt.argsOk
        iframe
        iunfold fmt.argsOk
        itrivial
      iapply HΦ
      iframe
      iunfold fmt.argOk
      iright; ileft
      iexact He3
  · wp_if_destruct
    · -- OnDelete
      wp_apply (wp_cleanupHistory dsc c cfg γa F γ ctx ds o d old rs) $$ [Htt Hold]
        as %e2 ⟨Htt, He2, Hold⟩
      · iframe #; iframe; ipureintro; exact Hctx
      cases e2 with
      | nil =>
        wp_auto
        iapply HΦ
        iframe
      | ok ei =>
        wp_auto
        wp_apply wp_slice_literal (V := GoInterface) [interface.ok ei]
        isplitr
        · ipureintro; rfl
        iintro %asl ⟨Hasl, -⟩
        wp_auto
        wp_apply (wp_Errorf _ _ [interface.ok ei] (DFrac.own 1)) $$ [Hasl He2] as %e3 ⟨-, #He3⟩
        · iframe
          iunfold fmt.argsOk
          iframe
          iunfold fmt.argsOk
          itrivial
        iapply HΦ
        iframe
        iunfold fmt.argOk
        iright; ileft
        iexact He3
    · wp_if_destruct
      · -- RollingUpdate
        wp_apply (wp_rollingUpdate dsc c cfg γa F γ ctx ds o d nl ns hash) $$ [Htt Hsync]
          as %e1 ⟨Htt, Hsync, He1⟩
        · iframe #
          iframe
          isplitr
          · ipureintro; exact Hctx
          · ipureintro; exact Hnd.2
        cases e1 with
        | ok ei =>
          wp_auto
          iapply HΦ
          iframe
        | nil =>
          wp_auto
          wp_apply (wp_cleanupHistory dsc c cfg γa F γ ctx ds o d old rs) $$ [Htt Hold]
            as %e2 ⟨Htt, He2, Hold⟩
          · iframe #; iframe; ipureintro; exact Hctx
          cases e2 with
          | nil =>
            wp_auto
            iapply HΦ
            iframe
          | ok ei =>
            wp_auto
            wp_apply wp_slice_literal (V := GoInterface) [interface.ok ei]
            isplitr
            · ipureintro; rfl
            iintro %asl ⟨Hasl, -⟩
            wp_auto
            wp_apply (wp_Errorf _ _ [interface.ok ei] (DFrac.own 1)) $$ [Hasl He2] as %e3 ⟨-, #He3⟩
            · iframe
              iunfold fmt.argsOk
              iframe
              iunfold fmt.argsOk
              itrivial
            iapply HΦ
            iframe
            iunfold fmt.argOk
            iright; ileft
            iexact He3
      · -- another strategy
        wp_apply (wp_cleanupHistory dsc c cfg γa F γ ctx ds o d old rs) $$ [Htt Hold]
          as %e2 ⟨Htt, He2, Hold⟩
        · iframe #; iframe; ipureintro; exact Hctx
        cases e2 with
        | nil =>
          wp_auto
          iapply HΦ
          iframe
        | ok ei =>
          wp_auto
          wp_apply wp_slice_literal (V := GoInterface) [interface.ok ei]
          isplitr
          · ipureintro; rfl
          iintro %asl ⟨Hasl, -⟩
          wp_auto
          wp_apply (wp_Errorf _ _ [interface.ok ei] (DFrac.own 1)) $$ [Hasl He2] as %e3 ⟨-, #He3⟩
          · iframe
            iunfold fmt.argsOk
            iframe
            iunfold fmt.argsOk
            itrivial
          iapply HΦ
          iframe
          iunfold fmt.argOk
          iright; ileft
          iexact He3

end proof

end dsctl
end EtcdGrove
end Perennial
