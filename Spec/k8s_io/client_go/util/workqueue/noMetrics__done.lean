/-
`noMetrics[T].done` (`metrics.go`): the metrics of an unnamed queue, a no-op. Lean-first.
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

/-- `noMetrics.done`: nothing happens. -/
abbrev noMetrics.done.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T] (v : noMetrics K) (k : K),
  {{ (True : IProp GF) }}
    (App (Val (v @!! noMetrics.ty T @!! go!"done")) (Val #k))
  {{ RET #(); True }}

end spec

end workqueue
end EtcdGrove
end Perennial
