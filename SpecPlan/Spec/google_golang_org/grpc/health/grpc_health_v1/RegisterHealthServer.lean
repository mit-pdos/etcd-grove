/-
`grpc_health_v1.RegisterHealthServer(s, srv)` (grpc-go, assumed: generated
`health/grpc_health_v1/health_grpc.pb.go:216`).

Users: `v3rpc.Server` (`grpc.go:98`).

Why true: `s.RegisterService(&Health_ServiceDesc, srv)`: the health service's `Check` and `List`
and the stream `Watch` registered with grpc's own handlers and the health server.

Changes: restored (round 1): the registrations are in `B` (the round-0 claim that they are not
contradicted `RegisterService.spec`); their contracts are `V3rpc.etcdContract`'s health entries,
met by grpc's health handlers (`V3rpc.healthRegs_ok`).

Margin: none.
-/
module

public import SpecPlan.Spec.google_golang_org.grpc.Api
public import GeneratedProof.google_golang_org.grpc.health
public import GeneratedProof.google_golang_org.grpc.health.grpc_health_v1
public import SpecPlan.Spec.PkgInit.google_golang_org.grpc.health.grpc_health_v1

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Grpc

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `RegisterHealthServer(gs, hs)`: the health service's registrations added. -/
def grpc_health_v1.RegisterHealthServer.spec : Prop :=
  ∀ (gs hs : Loc) (B : SrvCfg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.health.grpc_health_v1 ∗ srvBuild gs B ∗ healthAt hs }}
    (App (App (Val (@! google_golang_org.grpc.health.grpc_health_v1.RegisterHealthServer)) (Val #gs))
      (Val #(interface.mkOk (go.GoType.PointerType google_golang_org.grpc.health.Server.ty) #hs)))
  {{ RET #(); srvBuild gs { B with
        regs := B.regs ++ healthMethods.map (fun m => (m.1, m.2, interface.mkOk (go.GoType.PointerType google_golang_org.grpc.health.Server.ty) #hs)),
        sregs := B.sregs ++ healthStreams.map (fun m => (m.1, m.2, interface.mkOk (go.GoType.PointerType google_golang_org.grpc.health.Server.ty) #hs)) } }}

end spec

end Grpc
end EtcdGrove
end Perennial
