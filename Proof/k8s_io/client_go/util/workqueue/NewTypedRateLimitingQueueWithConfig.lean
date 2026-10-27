/-
Proof of `Spec/k8s_io/client_go/util/workqueue/NewTypedRateLimitingQueueWithConfig.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.NewTypedRateLimitingQueueWithConfig
public import Spec.k8s_io.client_go.util.workqueue.NewTypedDelayingQueueWithConfig

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace workqueue

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.util.workqueue

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.workqueue.Assumptions]

theorem NewTypedRateLimitingQueueWithConfig.wp_proof
    (wp_NewTypedDelayingQueueWithConfig :
      NewTypedDelayingQueueWithConfig.spec (GF := GF) (hG := hG)) :
    NewTypedRateLimitingQueueWithConfig.spec (GF := GF) (hG := hG) := by
  intro K T _ rl P cfg Hcfg
  obtain ⟨hl, hc, hq, hn⟩ := Hcfg
  rcases cfg with ⟨lg, nm, mp, ck, dq⟩
  simp only at hl hc hq hn
  subst hl hq
  wp_start as #Hrl
  wp_auto
  iStructNamed config
  rcases hc with rfl | rfl
  all_goals
    (try wp_auto)
    wp_apply (wp_NewTypedDelayingQueueWithConfig (K := K) (T := T)
      (TypedDelayingQueueConfig.mk Loc.null nm mp (interface.mkOk k8s_io.utils.clock.RealClock.ty
        #(zero_val k8s_io.utils.clock.RealClock)) GoInterface.nil) ⟨rfl, Or.inr rfl, rfl, hn⟩)
      as %dq %γ ⟨#Hdq, Htoks⟩
    wp_alloc r as Hr
    iStructNamed Hr
    ipersist TypedDelayingInterface
    ipersist rateLimiter
    wp_auto
    iapply HΦ
    iframe
    unfold isRateLimitingQueue
    iexists dq, rl
    iframe #

end proof

end workqueue
end EtcdGrove
end Perennial
