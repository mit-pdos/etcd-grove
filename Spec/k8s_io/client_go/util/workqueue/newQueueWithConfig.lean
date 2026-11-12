/-
`newQueueWithConfig[T](config, updatePeriod)` (`queue.go`): the defaults (the global metrics
provider, the real clock, the slice FIFO), then `newQueue`. Lean-first; for the default FIFO and
no metrics.
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

/-- `newQueueWithConfig(config, period)` for such a configuration: a typed queue. -/
abbrev newQueueWithConfig.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T] (cfg : TypedQueueConfig K)
    (period : time.Duration),
  queueConfigOk cfg →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue }}
    (App (App (Val #(functions newQueueWithConfig [T])) (Val #cfg)) (Val #period))
  {{ (q : Loc) (γ : QNames), RET #q; isTyped (K := K) q γ ∗ shutdownToks γ shutdownPool }}

end spec

end workqueue
end EtcdGrove
end Perennial
