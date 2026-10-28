/-
`(*delayingType[T]).waitingLoop(logger)` (`delaying_queue.go`): the delaying queue's goroutine.
Until the queue shuts down: adds the waiting entries whose time has come, sleeps until the next
one's time, the heartbeat, a stop, or a new entry, which it adds at once if due and otherwise
inserts in the heap (keeping the earlier time for an item already waiting); then drains the
entry channel the same way. Lean-first.
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

/-- `q.waitingLoop(logger)`: returns (when the queue shuts down), without panicking. -/
abbrev delayingType.waitingLoop.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T] (q : Loc) (γ : DNames)
    (logger : github_com.go_logr.logr.Logger),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue ∗ isDelaying (K := K) q γ }}
    (App (Val (q @!! go.GoType.PointerType (delayingType.ty T) @!! go!"waitingLoop")) (Val #logger))
  {{ RET #(); True }}

end spec

end workqueue
end EtcdGrove
end Perennial
