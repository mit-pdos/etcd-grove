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

/-- `rkv.Txn(ctx, in, opts...)` on a `*retryKVClient` over a stub on a connection to `addr`:
`rkv.kc.Txn(ctx, in, opts...)`: the call's answer (`txnCallOut`). -/
abbrev retryKVClient.Txn.spec : Prop :=
  ∀ (rkv conn : Loc) (addr : List GoString) (Spec : GrpcSpec (GF := GF) pbTxnRequest pbTxnResponse)
    (Q : TxnRespM → IProp GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (inp : Loc) (req : etcdserverpb.TxnRequest) (t : TxnModel) (opts : GoSlice)
    (vs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ retryKVAt rkv conn ∗
      isEtcdConn conn addr ∗ isGrpcRpcs addr go!"/etcdserverpb.KV/Txn" Spec ∗
      reqPre conn go!"/etcdserverpb.KV/Txn" addr vs (Spec t Q) ∗ ctxOk ctx cd ∗ inp ↦ req ∗ txnReqAt req t ∗
      opts ↦*□ vs ∗ callOptsOk vs }}
    (App (App (App (Val (rkv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.retryKVClient.ty @!!
        go!"Txn")) (Val #(GoInterface.ok ctx))) (Val #inp)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (∃ req' : etcdserverpb.TxnRequest, inp ↦ req') ∗ txnCallOut Q resp err }}

end spec

end EtcdGrove
end Perennial
