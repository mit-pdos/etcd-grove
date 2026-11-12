/-
`NewTypedItemExponentialFailureRateLimiter[T](baseDelay, maxDelay)` (`default_rate_limiters.go`). Lean-first.
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.workqueue.Assumptions]

/-- `NewTypedItemExponentialFailureRateLimiter(base, max)`: a rate limiter whose `When` returns
at most `max`. -/
abbrev NewTypedItemExponentialFailureRateLimiter.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T] (base max : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue }}
    (App (App (Val #(functions NewTypedItemExponentialFailureRateLimiter [T])) (Val #base)) (Val #max))
  {{ (rl : TypedRateLimiter K), RET #rl; isRateLimiter (K := K) rl (fun d => sint.Z d ≤ sint.Z max) }}

end spec

end workqueue
end EtcdGrove
end Perennial
