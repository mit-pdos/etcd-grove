/-
`RegisterLockServer(s, srv)` (`v3lockpb/*_grpc.pb.go`, generated).

Users: etcd's embed (`server/embed/serve.go:184-186` insecure, `:244-246` secure): after
`v3rpc.Server`, the lock service is registered on the member's server (2e).
Proof sketch: the assertion `srv.(interface{ testEmbeddedByValue() })` fails (etcd's service value
embeds no `UnimplementedLockServer`), then `s.RegisterService(&Lock_ServiceDesc, srv)` (2a's
`Server.RegisterService.spec` with `lockDesc_init`). The registrations then meet
`V3rpc.etcdContract`'s entries for the service (`etcdLocal`, a trivial stream contract): each
generated handler's run returns (2e's `lockServer.*` specs), which `regsOk` needs.
Changes: new (verify-round, A6-completeness F4: the registration was in no spec, and
`etcdContract` had no entry for the service, so a member started by embed met no contract).
Margin: the contract promises a gRPC client nothing of the service (no gRPC client of it is in
scope: the in-process `v3client` it runs over is open question 1.5).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3lock.v3lockpb.Api
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3lockpb

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `RegisterLockServer(s, srv)`: the registrar's `RegisterService` of the service's descriptor
(WP form). -/
def RegisterLockServer.spec : Prop :=
  ∀ (s : GoInterface) (srv : GoInterfaceOk) (Ψ : val → IProp GF),
  go.typeSetContains srv.ty EtcdServerPb.embedTestTy = false →
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3lock.v3lockpb ∗
    WP (App (App (Val (s @!! google_golang_org.grpc.ServiceRegistrar.ty @!! go!"RegisterService"))
      (Val #(globalAddr go_etcd_io.etcd.server.v3.etcdserver.api.v3lock.v3lockpb.Lock_ServiceDesc))) (Val #(GoInterface.ok srv))) {{ Ψ }} ⊢
  WP (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3lock.v3lockpb.RegisterLockServer)) (Val #s)) (Val #(GoInterface.ok srv))) {{ Ψ }}

end spec

end V3lockpb
end EtcdGrove
end Perennial
