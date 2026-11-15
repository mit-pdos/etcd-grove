/-
`v3rpc.NewClusterServer` (`server/etcdserver/api/v3rpc/`).

Users: `v3rpc.Server` (registration), `NewQuota*` wrappers.

Proof sketch: `s.Cluster()` (2e's membership), the server.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/NewClusterServer.lean`: over `isServer` (was the server's bundle of field readers).

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

/-- `NewClusterServer(s)`: the service object over `s`. -/
def NewClusterServer.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ isServer s γ }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.NewClusterServer)) (Val #s))
  {{ (p : Loc), RET #p; clusterServerAt p s γ }}

end spec

end V3rpc
end EtcdGrove
end Perennial
