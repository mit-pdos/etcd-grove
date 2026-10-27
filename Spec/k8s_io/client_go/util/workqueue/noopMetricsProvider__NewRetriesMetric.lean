/-
`noopMetricsProvider.NewRetriesMetric(name)` (`metrics.go`): the no-op provider's retries metric.
Lean-first.
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.workqueue.Assumptions]

/-- `noopMetricsProvider{}.NewRetriesMetric(name)`: the no-op metric. -/
abbrev noopMetricsProvider.NewRetriesMetric.spec : Prop :=
  ∀ (p : noopMetricsProvider) (name : GoString),
  {{ (True : IProp GF) }}
    (App (Val (p @!! noopMetricsProvider.ty @!! go!"NewRetriesMetric")) (Val #name))
  {{ RET #(noopCounter : CounterMetric); True }}

end spec

end workqueue
end EtcdGrove
end Perennial
