/-
`(*TypedItemFastSlowRateLimiter[T]).NumRequeues(item)` (`default_rate_limiters.go`): under the limiter's mutex, the item's failure count read. Lean-first.
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

/-- `r.NumRequeues(item)`. -/
abbrev TypedItemFastSlowRateLimiter.NumRequeues.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T] (r : Loc) (fast slow : time.Duration) (k : K),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue ∗ isFastSlowLimiter (K := K) r fast slow }}
    (App (Val (r @!! go.GoType.PointerType (TypedItemFastSlowRateLimiter.ty T) @!! go!"NumRequeues")) (Val #k))
  {{ (n : w64), RET #n; True }}

end spec

end workqueue
end EtcdGrove
end Perennial
