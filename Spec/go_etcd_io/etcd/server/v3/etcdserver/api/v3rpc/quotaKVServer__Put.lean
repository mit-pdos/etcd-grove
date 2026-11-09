/-
`quotaKVServer.Put` (`server/etcdserver/api/v3rpc/`).

Users: grpc's run of `/etcdserverpb.KV/Put` (the generated `_KV_Put_Handler`, 3h,
registered by `v3rpc.Server`); W0's `RemoteKV.*Triple` through grpc and the stub (`examples/specreq/clientv3kv/`, `examples/specreq/v3rpc/kv.go`).

Proof sketch: `qa.check(ctx, r)` (`quotaAlarmer.check.spec`): over the quota, the member raises the `NOSPACE` alarm (through raft: an environment step at its apply, 2d's `envUpd`) and the handler fires the caller's update with the refusal `.noSpace` (`Step.refuse`), returning `ErrGRPCNoSpace`; else the wrapped `KVServer`'s `Put` (`kvServer.Put.spec` at the `*kvServer` `quotaKVAt` holds).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/quotaKVServer__Put.lean`: no `backendUnderQuota` premise (the refusal is an answer).

Round 1: the contract is the member's at `ep` (`etcdContract γ ep`; the lease requests' `leaseFact`); the first way fires no token or learner refusal (`firedAns`: 2c returns an apply-time `ErrUserEmpty`/`ErrAuthOldRevision`/`ErrInvalidAuthToken` unfired, its outcome 2, which this handler sends by the second way); errors reach `togRPCError` with 2c's `srvErrOk`; a read composes with 2c's `SrvCallTriple` once W0's round 4 makes `srvStep` `Step` (a read's permission checked at an auth state between the call's start and its answer).

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

/-- `quotaKVServer.Put(ctx, r)` meets the contract of `/etcdserverpb.KV/Put`. -/
def quotaKVServer.Put.spec : Prop :=
  ∀ (p : Loc) (kv : GoInterface) (s : Loc) (γ : Cluster) (ep : GoString),
  HandlerTriple (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty @!! go!"Put")
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ quotaKVAt p kv s γ) (etcdUnary γ ep go!"/etcdserverpb.KV/Put") go_etcd_io.etcd.api.v3.etcdserverpb.PutRequest.ty go_etcd_io.etcd.api.v3.etcdserverpb.PutResponse.ty

end spec

end V3rpc
end EtcdGrove
end Perennial
