/-
`(*delayingType[T]).Len` (`delaying_queue.go`): promoted from the embedded
`TypedInterface[T]` field (Go's method set of `*delayingType[T]`, a wrapper
that calls `q.TypedInterface.Len`). Lean-first.

The spec is what follows from the embedded `Typed.Len`'s.
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

/-- `(*delayingType[T]).Len`, the method `delayingType` promotes from its embedded `TypedInterface`: `Len()`, as `Typed.Len`
on the embedded queue. -/
abbrev delayingType.Len.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T] (q : Loc) (γ : DNames) ,
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue ∗ isDelaying (K := K) q γ }}
    (App (Val (q @!! go.GoType.PointerType (delayingType.ty T) @!! go!"Len")) (Val #()))
  {{ (n : w64), RET #n; ⌜0 ≤ sint.Z n⌝ }}

end spec

end workqueue
end EtcdGrove
end Perennial
