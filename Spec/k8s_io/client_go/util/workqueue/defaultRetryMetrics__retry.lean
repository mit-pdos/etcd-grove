/-
`(*defaultRetryMetrics).retry()` (`metrics.go`): count a retry, nothing for a nil receiver.
Lean-first; the nil receiver and the no-op metric only.
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

/-- `m.retry()` on a nil `m` or one counting into the no-op metric: returns. -/
abbrev defaultRetryMetrics.retry.spec : Prop :=
  ∀ (m : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.workqueue ∗ defaultRetryOk m }}
    (App (Val (m @!! go.GoType.PointerType defaultRetryMetrics.ty @!! go!"retry")) (Val #()))
  {{ RET #(); True }}

end spec

end workqueue
end EtcdGrove
end Perennial
