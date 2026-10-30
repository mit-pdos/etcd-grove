/-
`(*TypedMaxOfRateLimiter[T]).Forget(item)` (`default_rate_limiters.go`): `Forget` on every limiter. Lean-first.
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

/-- `r.Forget(item)`. -/
abbrev TypedMaxOfRateLimiter.Forget.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T] (r : Loc) (k : K),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue ∗ isMaxOfLimiter (K := K) r }}
    (App (Val (r @!! go.GoType.PointerType (TypedMaxOfRateLimiter.ty T) @!! go!"Forget")) (Val #k))
  {{ RET #(); True }}

end spec

end workqueue
end EtcdGrove
end Perennial
