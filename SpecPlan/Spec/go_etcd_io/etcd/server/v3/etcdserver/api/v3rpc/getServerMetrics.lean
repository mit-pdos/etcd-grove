/-
`v3rpc.getServerMetrics` (`server/etcdserver/api/v3rpc/`).

Users: `v3rpc.Server`.

Proof sketch: the package's lock and cache; grpc-prometheus's `NewServerMetrics` and `prometheus.Register` (assumed: `metricsOk`), a warning logged on a registration error (`Zap.isLogger`, W0's).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/getServerMetrics.lean`.

Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3rpc

open Iris Iris.BI EtcdModel EtcdWire ClientV3 Grpc Proto EtcdServer

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `getServerMetrics(metricType, lg)`: grpc-prometheus's metrics (cached). -/
def getServerMetrics.spec : Prop :=
  ∀ (mt : GoString) (lg : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ Zap.isLogger lg }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.getServerMetrics)) (Val #mt)) (Val #lg))
  {{ (m : Loc), RET #m; metricsOk m }}

end spec

end V3rpc
end EtcdGrove
end Perennial
