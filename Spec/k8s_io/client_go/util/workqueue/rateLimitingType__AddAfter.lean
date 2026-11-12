/-
`(*rateLimitingType[T]).AddAfter` (`rate_limiting_queue.go`): promoted from the embedded
`TypedDelayingInterface[T]` field (Go's method set of `*rateLimitingType[T]`, a wrapper
that calls `q.TypedDelayingInterface.AddAfter`). Lean-first.

The spec is what follows from the embedded `delayingType.AddAfter`'s.
-/
module

public import Proof.k8s_io.client_go.util.workqueue.DelayingDefs

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

/-- `(*rateLimitingType[T]).AddAfter`, the method `rateLimitingType` promotes from its embedded `TypedDelayingInterface`: `AddAfter(item, d)`, as `delayingType.AddAfter`
on the embedded queue. -/
abbrev rateLimitingType.AddAfter.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T] (q : Loc) (γ : DNames) (P : time.Duration → Prop) (k : K) (d : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue ∗ isRateLimitingQueue (K := K) q γ P }}
    (App (App (Val (q @!! go.GoType.PointerType (rateLimitingType.ty T) @!! go!"AddAfter")) (Val #k)) (Val #d))
  {{ RET #(); True }}

end spec

end workqueue
end EtcdGrove
end Perennial
