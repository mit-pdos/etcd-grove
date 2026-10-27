/-
`(*clientv3.retryKVClient).Put(ctx, in, opts...)` (`client/v3/retry.go`, translated for unit C1, the client meets the server). Lean-first (no Rocq counterpart).
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

/-- `rkv.Put(ctx, in, opts...)` on a `*retryKVClient` over a stub on a connection to `addr`:
`rkv.kc.Put(ctx, in, opts...)`: the call's answer (`putCallOut`). -/
abbrev retryKVClient.Put.spec : Prop :=
  ∀ (rkv conn : Loc) (addr : List GoString) (Spec : GrpcSpec (GF := GF) pbPutRequest pbPutResponse)
    (Q : PutRespM → IProp GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (inp : Loc) (req : etcdserverpb.PutRequest) (k v : GoString) (opts : GoSlice)
    (vs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ retryKVAt rkv conn ∗
      isEtcdConn conn addr ∗ isGrpcRpcs addr go!"/etcdserverpb.KV/Put" Spec ∗
      reqPre conn go!"/etcdserverpb.KV/Put" addr vs (Spec (putReqOp req k v) Q) ∗ ctxOk ctx cd ∗ inp ↦ req ∗ req.Key' ↦*□ k ∗ req.Value' ↦*□ v ∗
      opts ↦*□ vs ∗ callOptsOk vs }}
    (App (App (App (Val (rkv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.retryKVClient.ty @!!
        go!"Put")) (Val #(GoInterface.ok ctx))) (Val #inp)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (∃ req' : etcdserverpb.PutRequest, inp ↦ req') ∗ putCallOut Q resp err }}

end spec

end EtcdGrove
end Perennial
