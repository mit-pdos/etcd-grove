/-
`quotaKVServer.Range` (`server/etcdserver/api/v3rpc/`).

Users: grpc's run of `/etcdserverpb.KV/Range` (the generated `_KV_Range_Handler`, 3h,
registered by `v3rpc.Server`); W0's `RemoteKV.*Triple` through grpc and the stub (`examples/specreq/clientv3kv/`, `examples/specreq/v3rpc/kv.go`).

Proof sketch: the promoted method of the embedded `KVServer` (`kvServer.Range.spec`).

Changes: new (the promoted method, what grpc calls on the registered `*quotaKVServer`).

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

/-- `quotaKVServer.Range(ctx, r)` meets the contract of `/etcdserverpb.KV/Range`. -/
def quotaKVServer.Range.spec : Prop :=
  ∀ (p : Loc) (kv : GoInterface) (s : Loc) (γ : Cluster),
  HandlerTriple (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty @!! go!"Range")
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ quotaKVAt p kv s γ) (etcdUnary γ go!"/etcdserverpb.KV/Range") go_etcd_io.etcd.api.v3.etcdserverpb.RangeRequest.ty go_etcd_io.etcd.api.v3.etcdserverpb.RangeResponse.ty

end spec

end V3rpc
end EtcdGrove
end Perennial
