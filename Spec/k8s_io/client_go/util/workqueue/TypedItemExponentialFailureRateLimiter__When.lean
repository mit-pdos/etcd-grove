/-
`(*TypedItemExponentialFailureRateLimiter[T]).When(item)` (`default_rate_limiters.go`): counts the failure; `baseDelay * 2^failures`, capped at `maxDelay`. Lean-first.

The spec bounds the result above by `maxDelay` only: the conversion of the `float64` backoff to a `Duration` is uninterpreted in the model (`EtcdGrove.Float64ToInt64Semantics`), and Go's is out of range (implementation-defined, `math.MinInt64` on amd64) when the backoff is exactly `2^63`, which the cap `backoff > math.MaxInt64` lets through (`issues/k8s-workqueue-exponential-backoff-2to63.md`).
-/
module

public import Proof.k8s_io.client_go.util.workqueue.Defs
public import Proof.k8s_io.client_go.util.workqueue.RateLimiterDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace workqueue

open Iris Iris.BI k8s_io.client_go.util.workqueue

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.workqueue.Assumptions]

/-- `r.When(item)`: at most `maxDelay`. -/
abbrev TypedItemExponentialFailureRateLimiter.When.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T] (r : Loc) (max : time.Duration) (k : K),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue ∗ isExpLimiter (K := K) r max }}
    (App (Val (r @!! go.GoType.PointerType (TypedItemExponentialFailureRateLimiter.ty T) @!! go!"When")) (Val #k))
  {{ (d : time.Duration), RET #d; ⌜sint.Z d ≤ sint.Z max⌝ }}

end spec

end workqueue
end EtcdGrove
end Perennial
