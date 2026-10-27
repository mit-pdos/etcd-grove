/-
`NewTypedItemFastSlowRateLimiter[T](fastDelay, slowDelay, maxFastAttempts)` (`default_rate_limiters.go`). Lean-first.
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

/-- `NewTypedItemFastSlowRateLimiter(fast, slow, n)`: a rate limiter whose `When` returns `fast` or
`slow`. -/
abbrev NewTypedItemFastSlowRateLimiter.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T] (fast slow : time.Duration) (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue }}
    (App (App (App (Val #(functions NewTypedItemFastSlowRateLimiter [T])) (Val #fast)) (Val #slow)) (Val #n))
  {{ (rl : TypedRateLimiter K), RET #rl; isRateLimiter (K := K) rl (fun d => d = fast ∨ d = slow) }}

end spec

end workqueue
end EtcdGrove
end Perennial
