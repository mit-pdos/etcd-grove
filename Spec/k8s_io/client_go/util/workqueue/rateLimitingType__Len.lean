/-
`(*rateLimitingType[T]).Len` (`rate_limiting_queue.go`): promoted from the embedded
`TypedDelayingInterface[T]` field (Go's method set of `*rateLimitingType[T]`, a wrapper
that calls `q.TypedDelayingInterface.Len`). Lean-first.

The spec is what follows from the embedded `delayingType.Len`'s.
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

/-- `(*rateLimitingType[T]).Len`, the method `rateLimitingType` promotes from its embedded `TypedDelayingInterface`: `Len()`, as `delayingType.Len`
on the embedded queue.
`Pk` is the queue's item predicate (`isTyped`); the statement without it is the instance `Pk := fun
_ => True`. -/
abbrev rateLimitingType.Len.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T] (q : Loc) (γ : DNames) (Pk : K → Prop) (P : time.Duration → Prop) ,
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue ∗ isRateLimitingQueue (K := K) q γ Pk P }}
    (App (Val (q @!! go.GoType.PointerType (rateLimitingType.ty T) @!! go!"Len")) (Val #()))
  {{ (n : w64), RET #n; ⌜0 ≤ sint.Z n⌝ }}

end spec

end workqueue
end EtcdGrove
end Perennial
