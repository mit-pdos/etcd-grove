/-
`v3rpc.NewAuthServer` (`server/etcdserver/api/v3rpc/`).

Users: `v3rpc.Server` (registration), `NewQuota*` wrappers.

Proof sketch: the server as `Authenticator`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/NewAuthServer.lean`: over `isServer` (was the server's bundle of field readers).

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

/-- `NewAuthServer(s)`: the service object over `s`. -/
def NewAuthServer.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ isServer s γ }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.NewAuthServer)) (Val #s))
  {{ (p : Loc), RET #p; authServerAt p s γ }}

end spec

end V3rpc
end EtcdGrove
end Perennial
