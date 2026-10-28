/-
`(*etcdserverpb.kVClient).Put(ctx, in, opts...)` (`api/etcdserverpb/rpc_grpc.pb.go`, the generated
KV stub; translated for unit C1, the client meets the server). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvKVConn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `c.Put(ctx, in, opts...)` on a stub on a connection to the server at `addr` (`kvStubAt`),
for a metadata-indexed spec `Spec` the server registered for the method (since 2026-10-28, the auth
plan's E3zc; a plain one is `GrpcSpec.md`) and the caller's `Φ` at every metadata an attempt may
deliver (`attemptPre`): `Invoke` of
`"/etcdserverpb.KV/Put"` with `grpc.StaticMethod()` before the options, into a new
`*PutResponse`: the call's answer (`putCallOut`, the run's `Φ`); the request comes back. -/
abbrev kVClient.Put.spec : Prop :=
  ∀ (kc conn : Loc) (addr : List GoString) (Spec : GrpcSpecMd (GF := GF) pbPutRequest pbPutResponse)
    (Φ : PutRespM → IProp GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (inp : Loc) (req : etcdserverpb.PutRequest) (k v : GoString) (opts : GoSlice)
    (vs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ kvStubAt kc conn ∗
      isEtcdConn conn addr ∗ isGrpcRpcsMd addr go!"/etcdserverpb.KV/Put" Spec ∗
      reqPre conn go!"/etcdserverpb.KV/Put" addr vs (attemptPre conn (GoInterface.ok ctx) Spec (putReqOp req k v) Φ) ∗ ctxOk ctx cd ∗ inp ↦ req ∗ req.Key' ↦*□ k ∗ req.Value' ↦*□ v ∗
      opts ↦*□ vs ∗ callOptsOk vs }}
    (App (App (App (Val (kc @!! go.GoType.PointerType etcdserverpb.kVClient.ty @!! go!"Put"))
      (Val #(GoInterface.ok ctx))) (Val #inp)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (∃ req' : etcdserverpb.PutRequest, inp ↦ req') ∗ putCallOut Φ resp err }}

end spec

end EtcdGrove
end Perennial
