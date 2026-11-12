/-
`v3rpc.newHeader` (`server/etcdserver/api/v3rpc/`).

Users: `NewKVServer`, `NewLeaseServer`, `NewMaintenanceServer`.

Proof sketch: the server's cluster id and member id (2e's getters over `isServer`), the server as the raft status getter, a closure reading `s.KV().Rev()` (`isServer_kv`: the persistent `s.kv ↦□ w` with `srvWatchable s γ w`; `EtcdServer.KV.spec` at that points-to returns `w`; then `w.Rev()`, 3e).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/newHeader.lean`.
verify-round relay (server-core's RR request 3): the closure's `KV()` through `isServer_kv` (2c's `KV.spec` now takes the points-to).

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

/-- `newHeader(s)`: a header of `s`. -/
def newHeader.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ isServer s γ }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.newHeader)) (Val #s))
  {{ (h : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.header), RET #h; headerAt h s γ }}

end spec

end V3rpc
end EtcdGrove
end Perennial
