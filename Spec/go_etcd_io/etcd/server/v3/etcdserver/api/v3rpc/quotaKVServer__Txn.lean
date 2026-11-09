/-
`quotaKVServer.Txn` (`server/etcdserver/api/v3rpc/`).

Users: grpc's run of `/etcdserverpb.KV/Txn` (the generated `_KV_Txn_Handler`, 3h,
registered by `v3rpc.Server`); W0's `RemoteKV.*Triple` through grpc and the stub (`examples/specreq/clientv3kv/`, `examples/specreq/v3rpc/kv.go`).

Proof sketch: `qa.check(ctx, r)` (`quotaAlarmer.check.spec`): over the quota, the member raises the `NOSPACE` alarm (through raft: an environment step at its apply, 2d's `envUpd`) and the handler fires the caller's update with the refusal `.noSpace` (`Step.refuse`), returning `ErrGRPCNoSpace`; else the wrapped `KVServer`'s `Txn` (`kvServer.Txn.spec` at the `*kvServer` `quotaKVAt` holds).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/quotaKVServer__Txn.lean`: no `backendUnderQuota` premise (the refusal is an answer).

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

/-- `quotaKVServer.Txn(ctx, r)` meets the contract of `/etcdserverpb.KV/Txn`. -/
def quotaKVServer.Txn.spec : Prop :=
  ∀ (p : Loc) (kv : GoInterface) (s : Loc) (γ : Cluster),
  HandlerTriple (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer.ty @!! go!"Txn")
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ quotaKVAt p kv s γ) (etcdUnary γ go!"/etcdserverpb.KV/Txn") go_etcd_io.etcd.api.v3.etcdserverpb.TxnRequest.ty go_etcd_io.etcd.api.v3.etcdserverpb.TxnResponse.ty

end spec

end V3rpc
end EtcdGrove
end Perennial
