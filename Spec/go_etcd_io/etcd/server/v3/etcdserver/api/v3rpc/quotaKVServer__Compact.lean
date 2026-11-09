/-
`quotaKVServer.Compact` (`server/etcdserver/api/v3rpc/`).

Users: grpc's run of `/etcdserverpb.KV/Compact` (the generated `_KV_Compact_Handler`, 3h,
registered by `v3rpc.Server`); W0's `RemoteKV.*Triple` through grpc and the stub (`examples/specreq/clientv3kv/`, `examples/specreq/v3rpc/kv.go`).

Proof sketch: the promoted method of the embedded `KVServer` (`kvServer.Compact.spec`).

Changes: new (the promoted method, what grpc calls on the registered `*quotaKVServer`).

Round 1: the contract is the member's at `ep` (`etcdContract γ ep`; the lease requests' `leaseFact`); the first way fires no token or learner refusal (`firedAns`: 2c returns an apply-time `ErrUserEmpty`/`ErrAuthOldRevision`/`ErrInvalidAuthToken` unfired, its outcome 2, which this handler sends by the second way); errors reach `togRPCError` with 2c's `srvErrOk`; a read composes with 2c's `SrvCallTriple` (W0's `lo`, rounds 4-6; integration I3: the Api header's "Composition with 2c").

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

/-- `quotaKVServer.Compact(ctx, r)` meets the contract of `/etcdserverpb.KV/Compact`. -/
def quotaKVServer.Compact.spec : Prop :=
  ∀ (p : Loc) (kv : GoInterface) (s : Loc) (γ : Cluster) (ep : GoString),
  HandlerTriple (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty @!! go!"Compact")
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ quotaKVAt p kv s γ) (etcdUnary γ ep go!"/etcdserverpb.KV/Compact") go_etcd_io.etcd.api.v3.etcdserverpb.CompactionRequest.ty go_etcd_io.etcd.api.v3.etcdserverpb.CompactionResponse.ty

end spec

end V3rpc
end EtcdGrove
end Perennial
