/-
`etcdserverpb._Watch_Watch_Handler(srv, stream)` (`api/etcdserverpb/rpc_grpc.pb.go`, the generated
server-side handler of the Watch service's bidirectional stream: `srv.(WatchServer).Watch(
&grpc.GenericServerStream[WatchRequest, WatchResponse]{ServerStream: stream})`; the watch
slice's unit W-W). Lean-first (no Rocq counterpart); the vocabulary is
`Proof/google_golang_org/grpc/InvGrpcStream.lean`.
-/
module

public import Proof.google_golang_org.grpc.InvGrpcStream

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
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- **`_Watch_Watch_Handler(srv, stream)`** for a service value `srv` whose type implements
`WatchServer` (a method-set fact) and whose `Watch` meets `Spec` with the client's content `Up`
and the resource `S` (`grpcStreamHandlerOk`, on the wrapped server end), for messages whose types
are `*WatchRequest`/`*WatchResponse` (a fresh `new(WatchRequest)` is a message the receiver owns),
on a raw server end `stream` of a fresh stream (`srvRawStreamIs`, both tokens at `[]`, its
auxiliary name unset: `streamAuxTok`) with `Spec γ Dn` and `S`: wraps the stream and runs `srv.Watch` on it; returns (nothing promised). -/
abbrev etcdserverpb._Watch_Watch_Handler.spec : Prop :=
  ∀ (Req Rep : StreamMsg GF) (Up : Nat → Req.M → IProp GF) (Spec : StreamSpec Rep)
    (srv : GoInterfaceOk) (S : IProp GF) (γ : StreamNames) (Dn : Nat → Rep.M → IProp GF)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (st : GoInterface),
  Req.ty = etcdserverpb.WatchRequest.ty → Rep.ty = etcdserverpb.WatchResponse.ty →
  go.typeSetContains srv.ty etcdserverpb.WatchServer.ty = true →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      (□ ∀ l : Loc, l ↦ (zero_val etcdserverpb.WatchRequest) -∗ Req.own l) ∗
      grpcStreamHandlerOk #(methods srv.ty go!"Watch" srv.v) S Up Spec ∗ Spec γ Dn ∗ S ∗
      srvRawStreamIs st γ Req Rep Up Dn ci cd ∗ srvRecvTok (Req := Req) γ [] ∗
      srvSendTok (Rep := Rep) γ [] ∗ streamAuxTok γ }}
    (streamHandlerCall (@! etcdserverpb._Watch_Watch_Handler) #(GoInterface.ok srv) #st)
  {{ (err : GoInterface), RET #err; True }}

end spec

end EtcdGrove
end Perennial
