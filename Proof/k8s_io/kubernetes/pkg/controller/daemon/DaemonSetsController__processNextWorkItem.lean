/-
Proof of `Spec/k8s_io/kubernetes/pkg/controller/daemon/DaemonSetsController__processNextWorkItem.lean`
over its callees' specs. Lean-first; Stage 3 of the autoverify run: a stub.

The proof's plan: `Get` gives `keyTok` of a canonical key (the queue's item predicate `keyCanon`); open `s1Inv`: the
owner `ownerOf key` registered (else register it: a fresh `ownerTok`, bound `0` with
`infRvLb 0` from the pod informer's invariant), its entry holds `syncTok` (not `keyTok`: ours is
exclusive); take it, leave `keyTok`; call the sync handler (`isDsc`'s `syncHandler`:
`syncDaemonSet`); open `s1Inv` again, swap back; `Done`.
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__processNextWorkItem
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__syncDaemonSet
public import Spec.k8s_io.client_go.util.workqueue.rateLimitingType__Get
public import Spec.k8s_io.client_go.util.workqueue.rateLimitingType__Done
public import Spec.k8s_io.client_go.util.workqueue.rateLimitingType__Forget
public import Spec.k8s_io.client_go.util.workqueue.rateLimitingType__AddRateLimited
public import Spec.k8s_io.apimachinery.pkg.util.runtime.HandleError
public import Spec.fmt.Errorf
public import Proof.k8s_io.kubernetes.pkg.controller.daemon.S1Trade

@[expose] public section

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode apimodel k8s_io.kubernetes.pkg.controller.daemon

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.daemon.Assumptions]
variable [wq_sem : k8s_io.client_go.util.workqueue.Assumptions]
variable [fmt_sem : _root_.Perennial.fmt.Assumptions]

theorem DaemonSetsController.processNextWorkItem.wp_proof
    (wp_Get : workqueue.rateLimitingType.Get.spec (GF := GF) (hG := hG))
    (wp_Done : workqueue.rateLimitingType.Done.spec (GF := GF) (hG := hG))
    (wp_Forget : workqueue.rateLimitingType.Forget.spec (GF := GF) (hG := hG))
    (wp_AddRateLimited : workqueue.rateLimitingType.AddRateLimited.spec (GF := GF) (hG := hG))
    (wp_syncDaemonSet : DaemonSetsController.syncDaemonSet.spec (GF := GF) (hG := hG))
    (wp_Errorf : fmt.Errorf.spec (GF := GF) (hG := hG))
    (wp_HandleError : utilruntime.HandleError.spec (GF := GF) (hG := hG)) :
    DaemonSetsController.processNextWorkItem.spec (GF := GF) (hG := hG) := by
  intro dsc c cfg γa F γ ctx
  wp_start as ⟨#Henv, Htt, %Hctx⟩
  ihave Henv2 := Henv
  iunfold dscEnv at Henv2
  icases Henv2 with ⟨#Hpkg, #Hdsc, #Hapi, #Hs1⟩
  ihave Hdsc2 := Hdsc
  iNamed Hdsc2
  icases Hq with ⟨%P, #Hqq⟩
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply (wp_Get (K := GoString) c.q c.γq keyCanon P) as %key %quit Hres
  · iexact Hqq
  cases quit
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hres with ⟨Hk, %Hcan⟩
    iapply fupd_wp
    imod s1Inv_trade γ c key Hcan $$ [Hs1 Hk] with ⟨Hkt, Hback⟩
    · iframe #; iframe
    imodintro
    wp_auto
    wp_apply (wp_syncDaemonSet dsc c cfg γa F γ ctx key) $$ [Htt Hkt] as %err ⟨Htt, Hkt, Herr⟩
    · iframe #; iframe; ipureintro; exact Hctx
    iapply fupd_wp
    imod Hback $$ Hkt with Hk
    imodintro
    cases err with
    | nil =>
      wp_auto
      wp_apply (wp_Forget (K := GoString) c.q c.γq keyCanon P key)
      · iexact Hqq
      wp_apply (wp_Done (K := GoString) c.q c.γq keyCanon P key) $$ [Hk]
      · iframe #; iframe
      iapply HΦ
      iframe
      ileft; ipureintro; rfl
    | ok ei =>
      wp_auto
      wp_apply wp_slice_literal (V := GoInterface)
        [interface.mkOk go.string #key, GoInterface.ok ei]
      isplitr
      · ipureintro; rfl
      iintro %asl ⟨Hasl, -⟩
      wp_auto
      wp_apply (wp_Errorf _ _ [interface.mkOk go.string #key, GoInterface.ok ei] (DFrac.own 1))
        $$ [Hasl Herr] as %e3 ⟨-, #He3⟩
      · iframe
        simp only [fmt.argsOk]
        isplitr
        · simp only [interface.mkOk, fmt.argOk]
          ileft; ipureintro
          apply fmt.argWf_of_argsWf
          exact .cons_string _ _ .nil
        isplitl [Herr]
        · iexact Herr
        · itrivial
      wp_apply (wp_HandleError _)
      wp_apply (wp_AddRateLimited (K := GoString) c.q c.γq keyCanon P key)
      · iframe #; ipureintro; exact Hcan
      wp_apply (wp_Done (K := GoString) c.q c.γq keyCanon P key) $$ [Hk]
      · iframe #; iframe
      iapply HΦ
      iframe
      ileft; ipureintro; rfl
  · simp only [↓reduceIte]
    icases Hres with ⟨%hk, #Hsd⟩
    wp_auto
    iapply HΦ
    iframe
    iright
    iexact Hsd

end proof

end dsctl
end EtcdGrove
end Perennial
