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

/-- `c.Txn(ctx, in, opts...)` on a stub on a connection to the server at `addr` (`kvStubAt`),
for a spec `Spec` the server registered for the method and the caller's `Φ`: `Invoke` of
`"/etcdserverpb.KV/Txn"` with `grpc.StaticMethod()` before the options, into a new
`*TxnResponse`: the call's answer (`txnCallOut`, the run's `Φ`); the request comes back. -/
abbrev kVClient.Txn.spec : Prop :=
  ∀ (kc conn : Loc) (addr : List GoString) (Spec : GrpcSpec (GF := GF) pbTxnRequest pbTxnResponse)
    (Φ : TxnRespM → IProp GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (inp : Loc) (req : etcdserverpb.TxnRequest) (t : TxnModel) (opts : GoSlice)
    (vs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ kvStubAt kc conn ∗
      isEtcdConn conn addr ∗ isGrpcRpcs addr go!"/etcdserverpb.KV/Txn" Spec ∗
      reqPre conn go!"/etcdserverpb.KV/Txn" addr vs (Spec t Φ) ∗ ctxOk ctx cd ∗ inp ↦ req ∗ txnReqAt req t ∗
      opts ↦*□ vs ∗ callOptsOk vs }}
    (App (App (App (Val (kc @!! go.GoType.PointerType etcdserverpb.kVClient.ty @!! go!"Txn"))
      (Val #(GoInterface.ok ctx))) (Val #inp)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (∃ req' : etcdserverpb.TxnRequest, inp ↦ req') ∗ txnCallOut Φ resp err }}

end spec

end EtcdGrove
end Perennial
