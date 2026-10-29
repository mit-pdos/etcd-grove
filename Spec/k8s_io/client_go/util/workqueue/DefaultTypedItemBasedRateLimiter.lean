/-
`DefaultTypedItemBasedRateLimiter[T]()` (`default_rate_limiters.go`): an exponential failure
limiter from 1 ms to 1000 s. Lean-first.
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

/-- `DefaultTypedItemBasedRateLimiter()`: a rate limiter whose `When` returns at most 1000 s. -/
abbrev DefaultTypedItemBasedRateLimiter.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T],
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue }}
    (App (Val #(functions DefaultTypedItemBasedRateLimiter [T])) (Val #()))
  {{ (rl : TypedRateLimiter K), RET #rl;
      isRateLimiter (K := K) rl (fun d => sint.Z d ≤ sint.Z (W64 1000 * W64 1000000000)) }}

end spec

end workqueue
end EtcdGrove
end Perennial
