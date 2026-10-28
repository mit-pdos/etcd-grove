/-
Proof of `Spec/k8s_io/client_go/util/workqueue/TypedBucketRateLimiter__Forget.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.TypedBucketRateLimiter__Forget

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace workqueue

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.util.workqueue

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.workqueue.Assumptions]

theorem TypedBucketRateLimiter.Forget.wp_proof : TypedBucketRateLimiter.Forget.spec (GF := GF) (hG := hG) := by
  intro K T _ r k
  wp_start as #Hr
  wp_auto
  wp_end

end proof

end workqueue
end EtcdGrove
end Perennial
