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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `rkv.DeleteRange(ctx, in, opts...)` on a `*retryKVClient` over a stub on a connection to `addr`:
`rkv.kc.DeleteRange(ctx, in, opts...)`: the call's answer (`deleteCallOut`). -/
abbrev retryKVClient.DeleteRange.spec : Prop :=
  ∀ (rkv conn : Loc) (addr : GoString) (Spec : GrpcSpec (GF := GF) pbDeleteRangeRequest pbDeleteRangeResponse)
    (Q : DelRespM → IProp GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (inp : Loc) (req : etcdserverpb.DeleteRangeRequest) (k e : GoString) (opts : GoSlice)
    (vs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ retryKVAt rkv conn ∗
      isEtcdConn conn addr ∗ isGrpcRpc addr go!"/etcdserverpb.KV/DeleteRange" Spec ∗
      □ ▷ Spec (deleteReqOp req k e) Q ∗ ctxOk ctx cd ∗ inp ↦ req ∗ req.Key' ↦*□ k ∗ req.RangeEnd' ↦*□ e ∗
      opts ↦*□ vs ∗ callOptsOk vs }}
    (App (App (App (Val (rkv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.retryKVClient.ty @!!
        go!"DeleteRange")) (Val #(GoInterface.ok ctx))) (Val #inp)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (∃ req' : etcdserverpb.DeleteRangeRequest, inp ↦ req') ∗ deleteCallOut Q resp err }}

end spec

end EtcdGrove
end Perennial
