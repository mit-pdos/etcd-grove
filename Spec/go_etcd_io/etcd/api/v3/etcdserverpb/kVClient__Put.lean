/-
`(*etcdserverpb.kVClient).Put(ctx, in, opts...)` (`api/etcdserverpb/rpc_grpc.pb.go`, the generated
KV stub; translated for unit C1, the client meets the server). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvKVConn
public import Spec.go_etcd_io.etcd.client.v3.Client__connectionForContext

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `c.Put(ctx, in, opts...)` on a stub on a connection to the server at `addr` (`kvStubAt`),
for a spec `Spec` the server registered for the method and the caller's `Φ`: `Invoke` of
`"/etcdserverpb.KV/Put"` with `grpc.StaticMethod()` before the options, into a new
`*PutResponse`: the call's answer (`putCallOut`, the run's `Φ`); the request comes back. -/
abbrev kVClient.Put.spec : Prop :=
  ∀ (kc conn : Loc) (addr : List GoString) (Spec : GrpcSpec (GF := GF) pbPutRequest pbPutResponse)
    (Φ : PutRespM → IProp GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (inp : Loc) (req : etcdserverpb.PutRequest) (k v : GoString) (opts : GoSlice)
    (vs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ kvStubAt kc conn ∗
      isEtcdConn conn addr ∗ isGrpcRpcs addr go!"/etcdserverpb.KV/Put" Spec ∗
      reqPre conn go!"/etcdserverpb.KV/Put" addr vs (Spec (putReqOp req k v) Φ) ∗ ctxOk ctx cd ∗ inp ↦ req ∗ req.Key' ↦*□ k ∗ req.Value' ↦*□ v ∗
      opts ↦*□ vs ∗ callOptsOk vs }}
    (App (App (App (Val (kc @!! go.GoType.PointerType etcdserverpb.kVClient.ty @!! go!"Put"))
      (Val #(GoInterface.ok ctx))) (Val #inp)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (∃ req' : etcdserverpb.PutRequest, inp ↦ req') ∗ putCallOut Φ resp err }}

/-- `c.Put(ctx, in, opts...)` on a stub backed by `&routingClientConn{client: cl}` (`kvRoutingStubAt`,
PR #21765) when `poolConnFor chs o ≠ null`: acquires `cl.epMu.RLock()` via `routingClientConn.Invoke`,
resolves `conn := poolConnFor chs o`, and invokes `"/etcdserverpb.KV/Put"` on `conn`. -/
abbrev kVClient.Put_routing.spec : Prop :=
  ∀ (kc rcc cl mu mref : Loc) (dq1 : DFrac)
    (chs : GMap GoString go_etcd_io.etcd.client.v3.channel)
    (o : Option GoString) (addr : List GoString)
    (Spec : GrpcSpec (GF := GF) pbPutRequest pbPutResponse)
    (Φ : PutRespM → IProp GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (inp : Loc) (req : etcdserverpb.PutRequest) (k v : GoString) (opts : GoSlice)
    (vs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      kvRoutingStubAt kc rcc cl ∗
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"epMu" cl ↦{dq1} mu ∗
      sync.ownRWMutex mu (clientPoolInv cl mref chs) ∗
      clientv3.ctxChannelKeyIs (GoInterface.ok ctx) o ∗
      ⌜poolConnFor chs o ≠ null⌝ ∗
      isEtcdConn (poolConnFor chs o) addr ∗ isGrpcRpcs addr go!"/etcdserverpb.KV/Put" Spec ∗
      reqPre (poolConnFor chs o) go!"/etcdserverpb.KV/Put" addr vs (Spec (putReqOp req k v) Φ) ∗
      ctxOk ctx cd ∗ inp ↦ req ∗ req.Key' ↦*□ k ∗ req.Value' ↦*□ v ∗
      opts ↦*□ vs ∗ callOptsOk vs }}
    (App (App (App (Val (kc @!! go.GoType.PointerType etcdserverpb.kVClient.ty @!! go!"Put"))
      (Val #(GoInterface.ok ctx))) (Val #inp)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"epMu" cl ↦{dq1} mu ∗
      sync.ownRWMutex mu (clientPoolInv cl mref chs) ∗
      (∃ req' : etcdserverpb.PutRequest, inp ↦ req') ∗ putCallOut Φ resp err }}

end spec

end EtcdGrove
end Perennial
