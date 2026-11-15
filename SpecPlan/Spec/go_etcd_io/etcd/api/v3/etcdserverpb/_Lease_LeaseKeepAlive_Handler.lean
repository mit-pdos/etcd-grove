/-
`_Lease_LeaseKeepAlive_Handler(srv, stream)` (`api/etcdserverpb/rpc_grpc.pb.go`, generated): the server-side
stream handler of `/etcdserverpb.Lease/LeaseKeepAlive`.

Users: grpc's `Serve` (2a's `streamOk`, from `Lease_ServiceDesc`'s `StreamDesc`); the service's
method is 2a's (`LeaseServer.LeaseKeepAlive`).
Proof sketch: allocate `&grpc.GenericServerStream[LeaseKeepAliveRequest, LeaseKeepAliveResponse]{ServerStream: stream}`, assert the
service interface (the premise), call its `LeaseKeepAlive` on the wrapper.
Changes: new.
Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.api.v3.etcdserverpb.Api

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

/-- `_Lease_LeaseKeepAlive_Handler(srv, stream)`: the service's `LeaseKeepAlive` on a fresh typed wrapper of the stream (WP
form). -/
def _Lease_LeaseKeepAlive_Handler.spec : Prop :=
  ∀ (srv : GoInterfaceOk) (st : GoInterface) (Ψ : val → IProp GF),
  go.typeSetContains srv.ty etcdserverpb.LeaseServer.ty = true →
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
    (∀ x : Loc,
      x ↦ (google_golang_org.grpc.GenericServerStream.mk st :
        google_golang_org.grpc.GenericServerStream etcdserverpb.LeaseKeepAliveRequest etcdserverpb.LeaseKeepAliveResponse) -∗
      WP (App (Val #(methods srv.ty go!"LeaseKeepAlive" srv.v))
        (Val #(interface.mkOk (go.GoType.PointerType
          (google_golang_org.grpc.GenericServerStream.ty etcdserverpb.LeaseKeepAliveRequest.ty etcdserverpb.LeaseKeepAliveResponse.ty)) #x)))
        {{ Ψ }}) ⊢
  WP (App (App (Val (@! etcdserverpb._Lease_LeaseKeepAlive_Handler)) (Val #(GoInterface.ok srv))) (Val #st)) {{ Ψ }}

end spec

end EtcdServerPb
end EtcdGrove
end Perennial
