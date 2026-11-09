/-
`v3rpc.newStreamInterceptor` (`server/etcdserver/api/v3rpc/`).

Users: `v3rpc.Server` (the stream chain).

Proof sketch: `monitorLeader.spec`; per stream: the capability and learner checks (a learner serves only `Snapshot`), the metadata checks, with the require-leader key a `cancellableContext` over the stream's (registered in the streams map, canceled with `ErrGRPCNoLeader` by the monitor), then the handler once.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/newStreamInterceptor.lean`: as `sicEtcdOk`.

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

/-- `newStreamInterceptor(s)`: a stream interceptor preserving etcd's stream contracts. -/
def newStreamInterceptor.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ isServer s γ }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.newStreamInterceptor)) (Val #s))
  {{ (i : GoFunc), RET #i; sicEtcdOk i γ }}

end spec

end V3rpc
end EtcdGrove
end Perennial
