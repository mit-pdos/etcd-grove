/-
`RangeSecObserve(success, latency)` (`metrics.go`, names-only), internal (`Range`'s deferred
metric): trust boundary, it records a latency. Old spec: same.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Txn

open Iris Iris.BI EtcdModel EtcdWire

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- `RangeSecObserve(...)` returns. -/
def RangeSecObserve.spec : Prop :=
  ∀ (success : Bool) (latency : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.RangeSecObserve)) (Val #success)) (Val #latency))
  {{ RET #(); True }}

end spec
end Txn
end EtcdGrove
end Perennial
