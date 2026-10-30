/-
`newQueueMetrics[T](mp, name, clock)` (`metrics.go`): no metrics for an unnamed queue or the no-op
provider, else the provider's metrics. Lean-first; the no-metrics cases only.
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

/-- `newQueueMetrics(mp, name, clock)` for an unnamed queue or the no-op provider: `noMetrics`. -/
abbrev newQueueMetrics.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T] (mp : MetricsProvider) (name : GoString)
    (c : k8s_io.utils.clock.Clock),
  name = [] ∨ mp = noopProvider →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue }}
    (App (App (App (Val #(functions newQueueMetrics [T])) (Val #mp)) (Val #name)) (Val #c))
  {{ RET #(noMetricsI (K := K) T); True }}

end spec

end workqueue
end EtcdGrove
end Perennial
