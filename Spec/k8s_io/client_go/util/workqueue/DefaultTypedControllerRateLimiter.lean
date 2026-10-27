/-
`DefaultTypedControllerRateLimiter[T]()` (`default_rate_limiters.go`): the max of an exponential
failure limiter (5 ms to 1000 s) and a token bucket (10 qps, burst 100). Lean-first.
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

/-- `DefaultTypedControllerRateLimiter()`: a rate limiter whose `When` returns a non-negative
duration (the DaemonSet controller's). -/
abbrev DefaultTypedControllerRateLimiter.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T],
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue }}
    (App (Val #(functions DefaultTypedControllerRateLimiter [T])) (Val #()))
  {{ (rl : TypedRateLimiter K), RET #rl; isRateLimiter (K := K) rl (fun d => 0 ≤ sint.Z d) }}

end spec

end workqueue
end EtcdGrove
end Perennial
