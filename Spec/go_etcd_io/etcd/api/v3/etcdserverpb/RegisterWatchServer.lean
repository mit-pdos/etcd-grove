/-
`RegisterWatchServer(s, srv)` (`api/etcdserverpb/rpc_grpc.pb.go`, generated).

Users: `v3rpc.Server` (`grpc.go`, 2a).
Proof sketch: the assertion `srv.(interface{ testEmbeddedByValue() })` fails (the premise: etcd's
service values embed no `UnimplementedWatchServer`), then `s.RegisterService(&Watch_ServiceDesc, srv)`.
2a's `Server.RegisterService.spec` with `watchDesc_init`/`otherDescs_init` gives the
registration.
Changes: from `specs-ref/Spec/go_etcd_io/etcd/api/v3/etcdserverpb/RegisterWatchServer.lean`: WP form (the registrar is grpc's, 2a's `Server.RegisterService.spec` at `*grpc.Server`).
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

/-- `RegisterWatchServer(s, srv)`: the registrar's `RegisterService` of the service's descriptor (WP form). -/
def RegisterWatchServer.spec : Prop :=
  ∀ (s : GoInterface) (srv : GoInterfaceOk) (Ψ : val → IProp GF),
  go.typeSetContains srv.ty embedTestTy = false →
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
    WP (App (App (Val (s @!! google_golang_org.grpc.ServiceRegistrar.ty @!! go!"RegisterService"))
      (Val #(globalAddr etcdserverpb.Watch_ServiceDesc))) (Val #(GoInterface.ok srv))) {{ Ψ }} ⊢
  WP (App (App (Val (@! etcdserverpb.RegisterWatchServer)) (Val #s)) (Val #(GoInterface.ok srv))) {{ Ψ }}

end spec

end EtcdServerPb
end EtcdGrove
end Perennial
