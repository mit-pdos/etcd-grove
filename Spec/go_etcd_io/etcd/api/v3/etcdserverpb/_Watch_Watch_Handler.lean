/-
`_Watch_Watch_Handler(srv, stream)` (`api/etcdserverpb/rpc_grpc.pb.go`, generated): the server-side
stream handler of `/etcdserverpb.Watch/Watch`.

Users: grpc's `Serve` (2a's `streamOk`, from `Watch_ServiceDesc`'s `StreamDesc`); the service's
method is 2b's (`watchServer.Watch`).
Proof sketch: allocate `&grpc.GenericServerStream[WatchRequest, WatchResponse]{ServerStream: stream}`, assert the
service interface (the premise), call its `Watch` on the wrapper.
Changes: from `specs-ref/Spec/go_etcd_io/etcd/api/v3/etcdserverpb/_Watch_Watch_Handler.lean`: WP form over grpc's server stream (2a's `streamOk` composes it).
Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.Api

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

/-- `_Watch_Watch_Handler(srv, stream)`: the service's `Watch` on a fresh typed wrapper of the stream (WP
form). -/
def _Watch_Watch_Handler.spec : Prop :=
  ∀ (srv : GoInterfaceOk) (st : GoInterface) (Ψ : val → IProp GF),
  go.typeSetContains srv.ty etcdserverpb.WatchServer.ty = true →
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
    (∀ x : Loc,
      x ↦ (google_golang_org.grpc.GenericServerStream.mk st :
        google_golang_org.grpc.GenericServerStream etcdserverpb.WatchRequest etcdserverpb.WatchResponse) -∗
      WP (App (Val #(methods srv.ty go!"Watch" srv.v))
        (Val #(interface.mkOk (go.GoType.PointerType
          (google_golang_org.grpc.GenericServerStream.ty etcdserverpb.WatchRequest.ty etcdserverpb.WatchResponse.ty)) #x)))
        {{ Ψ }}) ⊢
  WP (App (App (Val (@! etcdserverpb._Watch_Watch_Handler)) (Val #(GoInterface.ok srv))) (Val #st)) {{ Ψ }}

end spec

end EtcdServerPb
end EtcdGrove
end Perennial
