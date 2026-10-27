/-
Proof of `Spec/k8s_io/client_go/util/workqueue/defaultRetryMetrics__retry.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.defaultRetryMetrics__retry
public import Spec.k8s_io.client_go.util.workqueue.noopMetric__Inc

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

theorem defaultRetryMetrics.retry.wp_proof
    (wp_Inc : noopMetric.Inc.spec (GF := GF) (hG := hG)) :
    defaultRetryMetrics.retry.spec (GF := GF) (hG := hG) := by
  intro m
  wp_start as #Hm
  iunfold defaultRetryOk at Hm
  icases Hm with (%Hnil | #Hr)
  · subst Hnil
    wp_auto
    wp_end
  · wp_auto
    wp_if_destruct
    · wp_end
    · wp_apply (wp_Inc noopMetric.mk)
      wp_end

end proof

end workqueue
end EtcdGrove
end Perennial
