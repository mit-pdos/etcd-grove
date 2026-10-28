/-
`newQueue[T](c, queue, metrics, updatePeriod)` (`queue.go`): allocates the `Typed[T]` (empty
sets, a condition variable over a new mutex, the stop channel) and, unless `metrics` is
`noMetrics`, starts the unfinished-work goroutine. Lean-first.
-/
module

public import Proof.k8s_io.client_go.util.workqueue.Defs

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

/-- `newQueue(c, queue, noMetrics{}, period)` with the default FIFO (empty, at `l`): a typed
queue (`isTyped`) and its shutdown tokens. No goroutine is started. -/
abbrev newQueue.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T] (c : k8s_io.utils.clock.WithTicker)
    (l : Loc) (nm : noMetrics K) (period : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue ∗ ownFifo (GF := GF) (K := K) l [] }}
    (App (App (App (App (Val #(functions newQueue [T])) (Val #c))
        (Val #(interface.mkOk (go.GoType.PointerType (queue.ty T)) #l : Queue K)))
        (Val #(interface.mkOk (noMetrics.ty T) #nm : queueMetrics K))) (Val #period))
  {{ (q : Loc) (γ : QNames), RET #q; isTyped (K := K) q γ ∗ shutdownToks γ shutdownPool }}

end spec

end workqueue
end EtcdGrove
end Perennial
