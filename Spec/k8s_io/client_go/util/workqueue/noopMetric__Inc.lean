/-
`noopMetric.Inc` (`metrics.go`): the no-op metric's `Inc`. Lean-first.
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.workqueue.Assumptions]

/-- `noopMetric.Inc()`: nothing happens. -/
abbrev noopMetric.Inc.spec : Prop :=
  ∀ (v : noopMetric),
  {{ (True : IProp GF) }}
    (App (Val (v @!! noopMetric.ty @!! go!"Inc")) (Val #()))
  {{ RET #(); True }}

end spec

end workqueue
end EtcdGrove
end Perennial
