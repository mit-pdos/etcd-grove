/-
`(*delayingType[T]).AddAfter(item, duration)` (`delaying_queue.go`): nothing once shutting
down; at once for a non-positive delay; otherwise an entry (the item and its ready time) to the
waiting loop, or nothing if the queue shuts down first. Lean-first.
-/
module

public import Proof.k8s_io.client_go.util.workqueue.Defs
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

/-- `q.AddAfter(item, d)`: returns (it may block until the waiting loop takes the entry or the
queue shuts down). When the item is added is not stated (liveness). -/
abbrev delayingType.AddAfter.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T] (q : Loc) (γ : DNames) (k : K)
    (d : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue ∗ isDelaying (K := K) q γ }}
    (App (App (Val (q @!! go.GoType.PointerType (delayingType.ty T) @!! go!"AddAfter")) (Val #k))
      (Val #d))
  {{ RET #(); True }}

end spec

end workqueue
end EtcdGrove
end Perennial
