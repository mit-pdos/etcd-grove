/-
`_KV_RangeStream_Handler(srv, stream)` (`api/etcdserverpb/rpc_grpc.pb.go`, generated): the server-side
handler of the server-streaming `/etcdserverpb.KV/RangeStream`.

Users: grpc's `Serve` (2a's `streamOk`, from `KV_ServiceDesc`'s `StreamDesc`); the service's method
is 2a's `kvServer.RangeStream`.
Proof sketch: `new(RangeRequest)`, `stream.RecvMsg(m)` (2a's `srvRecv_recv`: the client's one request,
canonical, with the contract's `up`), its error returned; then the wrapper
`&grpc.GenericServerStream[...]{ServerStream: stream}` (persisted: grpc's `genSrvAt`) and the type
assertion `srv.(KVServer)` (the premise), the method on `(m, wrapper)` (`serverStreamHandlerWP`).
Blocked: the body is untranslated (names only in `Code/go_etcd_io/etcd/api/v3/etcdserverpb.toml`): the proof waits for its translation (open question 7.4).
Changes: verify-round: new (A6 completeness F1 / provability F9).
Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.api.v3.etcdserverpb.StreamShapes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServerPb

open Iris Iris.BI EtcdModel EtcdWire
open go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- `_KV_RangeStream_Handler(srv, stream)`: receive the one request, then the service's `RangeStream` on it and a
wrapper of the stream (WP form). -/
def _KV_RangeStream_Handler.spec : Prop :=
  ∀ (srv : GoInterfaceOk) (st : GoInterface) (Ψ : val → IProp GF),
  go.typeSetContains srv.ty etcdserverpb.KVServer.ty = true →
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
    serverStreamHandlerWP srv go!"RangeStream" etcdserverpb.RangeRequest.ty etcdserverpb.RangeStreamResponse.ty st Ψ ⊢
  WP (App (App (Val (@! etcdserverpb._KV_RangeStream_Handler)) (Val #(GoInterface.ok srv))) (Val #st)) {{ Ψ }}

end spec

end EtcdServerPb
end EtcdGrove
end Perennial
