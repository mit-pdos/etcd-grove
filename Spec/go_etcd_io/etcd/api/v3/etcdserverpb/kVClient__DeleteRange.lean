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

/-- `c.DeleteRange(ctx, in, opts...)` on a stub on a connection to the server at `addr` (`kvStubAt`),
for a metadata-indexed spec `Spec` the server registered for the method (since 2026-10-28, the auth
plan's E3zc; a plain one is `GrpcSpec.md`) and the caller's `Φ` at every metadata an attempt may
deliver (`attemptPre`): `Invoke` of
`"/etcdserverpb.KV/DeleteRange"` with `grpc.StaticMethod()` before the options, into a new
`*DeleteRangeResponse`: the call's answer (`deleteCallOut`, the run's `Φ`); the request comes back. The
request has no unknown fields (a struct literal) and its encoding is below `grpcMsgMax` (2026-10-30:
grpc marshals before it checks a size, `grpcInvokerOk`). -/
abbrev kVClient.DeleteRange.spec : Prop :=
  ∀ (kc conn : Loc) (addr : List GoString) (Spec : GrpcSpecMd (GF := GF) pbDeleteRangeRequest pbDeleteRangeResponse)
    (Φ : DelRespM → IProp GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (inp : Loc) (req : etcdserverpb.DeleteRangeRequest) (k e : GoString) (opts : GoSlice)
    (vs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ kvStubAt kc conn ∗
      isEtcdConn conn addr ∗ isGrpcRpcsMd addr go!"/etcdserverpb.KV/DeleteRange" Spec ∗
      reqPre conn go!"/etcdserverpb.KV/DeleteRange" addr vs (attemptPre conn (GoInterface.ok ctx) Spec (deleteReqOp req k e) Φ) ∗ ctxOk ctx cd ∗ inp ↦ req ∗ req.Key' ↦*□ k ∗ req.RangeEnd' ↦*□ e ∗
      opts ↦*□ vs ∗ callOptsOk vs ∗
      ⌜req.unknownFields' = slice.nil ∧ (pbDeleteRangeRequest (GF := GF)).wireLen (deleteReqOp req k e) < grpcMsgMax⌝ }}
    (App (App (App (Val (kc @!! go.GoType.PointerType etcdserverpb.kVClient.ty @!! go!"DeleteRange"))
      (Val #(GoInterface.ok ctx))) (Val #inp)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (∃ req' : etcdserverpb.DeleteRangeRequest, inp ↦ req') ∗ deleteCallOut Φ resp err }}

end spec

end EtcdGrove
end Perennial
