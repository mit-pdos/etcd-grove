/-
`ReportEventReceived(n)` (`metrics.go:318`): the watch metrics (`pendingEventsGauge.Sub`,
`totalEventsCounter.Add`). **Users**: v3rpc's watch send loop (`v3rpc/watch.go:426, 430, 477, 572`,
with `len(...)` of an events slice; 2b's req item 6). `n ≥ 0`: a Prometheus counter's `Add` panics
on a negative value (the callers pass a length).

**Changes** from `specs-ref`'s file: the premise in the precondition.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `ReportEventReceived(n)` (`n ≥ 0`): no panic. -/
def ReportEventReceived.spec : Prop :=
  ∀ n : w64,
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ ⌜0 ≤ sint.Z n⌝ }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.ReportEventReceived)) (Val #n))
  {{ RET #(); True }}

end spec
end Mvcc
end EtcdGrove
end Perennial
