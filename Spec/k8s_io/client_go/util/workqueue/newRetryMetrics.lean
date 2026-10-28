/-
`newRetryMetrics(name, provider)` (`metrics.go`): a nil `*defaultRetryMetrics` for an unnamed
queue, else one counting into the provider's (or the global provider's) retries metric.
Lean-first; the unnamed queue and the no-op providers only.
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

/-- `newRetryMetrics(name, provider)` for an unnamed queue, or the provider unset (so the global
no-op one) or the no-op one: retry metrics whose `retry()` returns. -/
abbrev newRetryMetrics.spec : Prop :=
  ∀ (name : GoString) (provider : MetricsProvider),
  name = [] ∨ provider = interface.nil ∨ provider = noopProvider →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue }}
    (App (App (Val #(functions newRetryMetrics [])) (Val #name)) (Val #provider))
  {{ (rm : retryMetrics), RET #rm; isRetryMetrics rm }}

end spec

end workqueue
end EtcdGrove
end Perennial
