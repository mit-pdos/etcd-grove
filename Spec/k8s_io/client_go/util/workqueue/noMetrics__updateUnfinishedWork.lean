/-
`noMetrics[T].updateUnfinishedWork` (`metrics.go`): the metrics of an unnamed queue, a no-op. Lean-first.
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

/-- `noMetrics.updateUnfinishedWork`: nothing happens. -/
abbrev noMetrics.updateUnfinishedWork.spec : Prop :=
  ∀ {K : Type} {T : go.GoType} [QItem (GF := GF) K T] (v : noMetrics K) ,
  {{ (True : IProp GF) }}
    (App (Val (v @!! noMetrics.ty T @!! go!"updateUnfinishedWork")) (Val #()))
  {{ RET #(); True }}

end spec

end workqueue
end EtcdGrove
end Perennial
