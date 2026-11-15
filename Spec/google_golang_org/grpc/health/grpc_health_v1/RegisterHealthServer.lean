/-
`grpc_health_v1.RegisterHealthServer(s, srv)` (generated, names only; item 4, the server start):
`v3rpc.Server` registers grpc's health server.
-/
module

public import Proof.google_golang_org.grpc.InvGrpcServer
public import GeneratedProof.google_golang_org.grpc.health.grpc_health_v1
public import GeneratedProof.google_golang_org.grpc.health

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `RegisterHealthServer(gs, hs)`, of grpc's health server on a server being built that has no
service `grpc.health.v1.Health` yet, registers that service: some methods and streams, with distinct
names, all under `/grpc.health.v1.Health/` (grpc v1.84's `Check`, `List` and `Watch`,
`health/grpc_health_v1/health_grpc.pb.go`; per-type stage B, B1b, the distinctness). Its one stream,
`Watch`, is `ServerStreams`, so the registration keeps `grpcSrvNew`'s invariant (every stream
descriptor sets a stream flag; checked by test T10b). -/
abbrev grpc_health_v1.RegisterHealthServer.spec : Prop :=
  ∀ (gs hs : Loc) (ics sics : List GoFunc) (svcs : List GoString)
    (regs sregs : List (GoString × GoFunc × GoInterface)),
  {{ grpcSrvNew (GF := GF) gs ics sics svcs regs sregs ∗ grpcHealthSrv hs ∗
      ⌜go!"grpc.health.v1.Health" ∉ svcs⌝ }}
    (App (App (Val (@! google_golang_org.grpc.health.grpc_health_v1.RegisterHealthServer))
      (Val #(interface.mkOk (go.GoType.PointerType google_golang_org.grpc.Server.ty) #gs : GoInterface)))
      (Val #(interface.mkOk (go.GoType.PointerType google_golang_org.grpc.health.Server.ty) #hs : GoInterface)))
  {{ RET #(); ∃ rs srs : List (GoString × GoFunc × GoInterface),
      grpcSrvNew gs ics sics (svcs ++ [go!"grpc.health.v1.Health"]) (regs ++ rs) (sregs ++ srs) ∗
      ⌜∀ x ∈ rs ++ srs, go!"/grpc.health.v1.Health/" <+: x.1⌝ ∗ ⌜((rs ++ srs).map Prod.fst).Nodup⌝ }}

end spec

end EtcdGrove
end Perennial
