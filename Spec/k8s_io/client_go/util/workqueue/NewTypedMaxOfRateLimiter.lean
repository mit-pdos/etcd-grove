/-
`NewTypedMaxOfRateLimiter[T](limiters...)` (`default_rate_limiters.go`). Lean-first.
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

/-- `NewTypedMaxOfRateLimiter(limiters...)` of rate limiters (the slice is kept, read-only for
good): a rate limiter whose `When` returns a non-negative duration. -/
abbrev NewTypedMaxOfRateLimiter.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T] (sl : GoSlice) (ls : List (TypedRateLimiter K)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue ∗ sl ↦* ls ∗
      [∗list] l ∈ ls, ∃ P : time.Duration → Prop, isRateLimiter (K := K) l P }}
    (App (Val #(functions NewTypedMaxOfRateLimiter [T])) (Val #sl))
  {{ (rl : TypedRateLimiter K), RET #rl; isRateLimiter (K := K) rl (fun d => 0 ≤ sint.Z d) }}

end spec

end workqueue
end EtcdGrove
end Perennial
