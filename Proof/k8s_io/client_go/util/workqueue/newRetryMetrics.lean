/-
Proof of `Spec/k8s_io/client_go/util/workqueue/newRetryMetrics.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.newRetryMetrics
public import Spec.k8s_io.client_go.util.workqueue.defaultRetryMetrics__retry
public import Spec.k8s_io.client_go.util.workqueue.noopMetricsProvider__NewRetriesMetric

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

/-- A `*defaultRetryMetrics` with `defaultRetryOk` is retry metrics. -/
theorem defaultRetry_isRetryMetrics
    (wp_retry : defaultRetryMetrics.retry.spec (GF := GF) (hG := hG)) (m : Loc) :
    defaultRetryOk (GF := GF) m ⊢
      isRetryMetrics (interface.mkOk (go.GoType.PointerType defaultRetryMetrics.ty) #m) := by
  iintro #Hm
  unfold isRetryMetrics
  iexists _
  isplitr
  · ipureintro; rfl
  iintro !> %Φ Hpkg HΦ
  iapply (wp_retry m) $$ [$Hpkg $Hm] HΦ

theorem newRetryMetrics.wp_proof
    (wp_retry : defaultRetryMetrics.retry.spec (GF := GF) (hG := hG))
    (wp_NewRetriesMetric : noopMetricsProvider.NewRetriesMetric.spec (GF := GF) (hG := hG)) :
    newRetryMetrics.spec (GF := GF) (hG := hG) := by
  intro name provider Hpre
  wp_start
  ihave #Hg := globalProvider_noop $$ Hpkg
  wp_auto
  wp_func_call
  wp_call
  by_cases hl : name.length < 2 ^ 63
  · rw [if_pos hl]
    wp_auto
    wp_if_destruct
    · iapply HΦ
      iapply (defaultRetry_isRetryMetrics wp_retry)
      unfold defaultRetryOk
      ileft; ipureintro; rfl
    · have hp : provider = interface.nil ∨ provider = noopProvider := by
        rcases Hpre with h | h
        · subst h; simp at Hif
        · exact h
      rcases hp with rfl | rfl
      all_goals
        wp_auto
        wp_apply (wp_NewRetriesMetric noopMetricsProvider.mk name)
        wp_alloc rm as Hrm
        iStructNamed Hrm
        ipersist retries
        wp_auto
        iapply HΦ
        iapply (defaultRetry_isRetryMetrics wp_retry)
        unfold defaultRetryOk
        iright
        iexact retries
  · rw [if_neg hl]
    wp_apply wp_AngelicExit

end proof

end workqueue
end EtcdGrove
end Perennial
