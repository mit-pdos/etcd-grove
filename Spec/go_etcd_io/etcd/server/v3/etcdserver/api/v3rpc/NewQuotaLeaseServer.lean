/-
`v3rpc.NewQuotaLeaseServer` (`server/etcdserver/api/v3rpc/`).

Users: `v3rpc.Server` (the registered KV and Lease values).

Proof sketch: `NewLeaseServer.spec`; a `quotaAlarmer{s, name}` (`quotaAlarmerAt`).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/NewQuotaLeaseServer.lean`: no quota premise.

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

/-- `NewQuotaLeaseServer(s)`: the quota wrapper over the service object. -/
def NewQuotaLeaseServer.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ isServer s γ }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.NewQuotaLeaseServer)) (Val #s))
  {{ (v : GoInterface), RET #v; ∃ (q : Loc) (kv : GoInterface),
      ⌜v = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty) #q⌝ ∗ quotaLeaseAt q kv s γ ∗ (∃ p, ⌜kv = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty) #p⌝ ∗ leaseServerAt p s γ) }}

end spec

end V3rpc
end EtcdGrove
end Perennial
