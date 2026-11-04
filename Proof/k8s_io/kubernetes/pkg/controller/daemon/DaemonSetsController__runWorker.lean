/-
Proof of `Spec/k8s_io/kubernetes/pkg/controller/daemon/DaemonSetsController__runWorker.lean` over its callees' specs. Lean-first; Stage 3 of the autoverify run
(track C, `notes/k8s-daemonset-run/design.md`): a stub.

The plan: a loop over `processNextWorkItem`'s spec.
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__runWorker
public import Spec.k8s_io.kubernetes.pkg.controller.daemon.DaemonSetsController__processNextWorkItem

@[expose] public section

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode apimodel informer informers cache workqueue k8s_io.kubernetes.pkg.controller.daemon

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.daemon.Assumptions]

theorem DaemonSetsController.runWorker.wp_proof
    (wp_processNextWorkItem : DaemonSetsController.processNextWorkItem.spec (GF := GF) (hG := hG)) :
    DaemonSetsController.runWorker.spec (GF := GF) (hG := hG) := by
  intro dsc c cfg γa F γ ctx
  wp_start as ⟨#Henv, Htt, %Hctx⟩
  ihave Henv2 := Henv
  iunfold dscEnv at Henv2
  icases Henv2 with ⟨#Hpkg, -, -, -⟩
  wp_auto
  ihave HI : (threadTok ∗ dsc_ptr ↦ dsc ∗ ctx_ptr ↦ ctx : IProp GF) $$ [Htt dsc ctx]
  · iframe
  wp_for HI
  icases HI with ⟨Htt, Hd, Hc⟩
  wp_auto
  wp_apply (wp_processNextWorkItem dsc c cfg γa F γ ctx) $$ [Htt] as %b ⟨Htt, Hb⟩
  · iframe #; iframe; ipureintro; exact Hctx
  have Hft : ¬ ((#false : val) = #true) := fun h => Bool.false_ne_true (go.intoVal_inj h)
  cases b
  · icases Hb with (%Hb | #Hsd)
    · cases Hb
    simp only [Hft, decide_false, Bool.false_eq_true, ↓reduceIte, _root_.decide_true]
    wp_auto
    iapply HΦ
    iframe
    iframe #
  · simp only [_root_.decide_true, ↓reduceIte]
    wp_auto
    wp_for_post
    unfold named
    iframe

end proof

end dsctl
end EtcdGrove
end Perennial
