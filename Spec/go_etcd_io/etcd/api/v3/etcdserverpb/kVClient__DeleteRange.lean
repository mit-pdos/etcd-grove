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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `c.DeleteRange(ctx, in, opts...)` on a stub on a connection to the server at `addr` (`kvStubAt`),
for a spec `Spec` the server registered for the method and the caller's `Φ`: `Invoke` of
`"/etcdserverpb.KV/DeleteRange"` with `grpc.StaticMethod()` before the options, into a new
`*DeleteRangeResponse`: the call's answer (`deleteCallOut`, the run's `Φ`); the request comes back. -/
abbrev kVClient.DeleteRange.spec : Prop :=
  ∀ (kc conn : Loc) (addr : List GoString) (Spec : GrpcSpec (GF := GF) pbDeleteRangeRequest pbDeleteRangeResponse)
    (Φ : DelRespM → IProp GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (inp : Loc) (req : etcdserverpb.DeleteRangeRequest) (k e : GoString) (opts : GoSlice)
    (vs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ kvStubAt kc conn ∗
      isEtcdConn conn addr ∗ isGrpcRpcs addr go!"/etcdserverpb.KV/DeleteRange" Spec ∗
      reqPre conn go!"/etcdserverpb.KV/DeleteRange" addr vs (Spec (deleteReqOp req k e) Φ) ∗ ctxOk ctx cd ∗ inp ↦ req ∗ req.Key' ↦*□ k ∗ req.RangeEnd' ↦*□ e ∗
      opts ↦*□ vs ∗ callOptsOk vs }}
    (App (App (App (Val (kc @!! go.GoType.PointerType etcdserverpb.kVClient.ty @!! go!"DeleteRange"))
      (Val #(GoInterface.ok ctx))) (Val #inp)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (∃ req' : etcdserverpb.DeleteRangeRequest, inp ↦ req') ∗ deleteCallOut Φ resp err }}

end spec

end EtcdGrove
end Perennial
