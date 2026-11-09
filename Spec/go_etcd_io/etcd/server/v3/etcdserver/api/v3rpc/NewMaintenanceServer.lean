/-
`v3rpc.NewMaintenanceServer` (`server/etcdserver/api/v3rpc/`).

Users: `v3rpc.Server`.

Proof sketch: the server's getters (hasher, backend, raft status, alarms, version adapter), `newHeader.spec`, the notifier; wrapped as an `authMaintenanceServer` with `&AuthAdmin{s}`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/NewMaintenanceServer.lean`.

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Api

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

/-- `NewMaintenanceServer(s, hn)`: the registered maintenance value. -/
def NewMaintenanceServer.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (hn : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ isServer s γ ∗ notifierAt hn }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.NewMaintenanceServer)) (Val #s)) (Val #hn))
  {{ (v : GoInterface), RET #v; ∃ p : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.authMaintenanceServer.ty) #p⌝ ∗ authMaintAt p s γ }}

end spec

end V3rpc
end EtcdGrove
end Perennial
