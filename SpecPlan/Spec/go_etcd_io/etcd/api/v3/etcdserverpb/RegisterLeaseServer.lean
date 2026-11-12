/-
`RegisterLeaseServer(s, srv)` (`api/etcdserverpb/rpc_grpc.pb.go`, generated).

Users: `v3rpc.Server` (`grpc.go`, 2a).
Proof sketch: the assertion `srv.(interface{ testEmbeddedByValue() })` fails (the premise: etcd's
service values embed no `UnimplementedLeaseServer`), then `s.RegisterService(&Lease_ServiceDesc, srv)`.
2a's `Server.RegisterService.spec` with `leaseDesc_init`/`otherDescs_init` gives the
registration.
Changes: from `specs-ref/Spec/go_etcd_io/etcd/api/v3/etcdserverpb/RegisterLeaseServer.lean`: WP form (the registrar is grpc's, 2a's `Server.RegisterService.spec` at `*grpc.Server`).
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

/-- `RegisterLeaseServer(s, srv)`: the registrar's `RegisterService` of the service's descriptor (WP form). -/
def RegisterLeaseServer.spec : Prop :=
  ∀ (s : GoInterface) (srv : GoInterfaceOk) (Ψ : val → IProp GF),
  go.typeSetContains srv.ty embedTestTy = false →
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
    WP (App (App (Val (s @!! google_golang_org.grpc.ServiceRegistrar.ty @!! go!"RegisterService"))
      (Val #(globalAddr etcdserverpb.Lease_ServiceDesc))) (Val #(GoInterface.ok srv))) {{ Ψ }} ⊢
  WP (App (App (Val (@! etcdserverpb.RegisterLeaseServer)) (Val #s)) (Val #(GoInterface.ok srv))) {{ Ψ }}

end spec

end EtcdServerPb
end EtcdGrove
end Perennial
