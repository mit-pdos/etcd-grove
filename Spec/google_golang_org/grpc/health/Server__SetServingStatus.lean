/-
`(*health.Server).SetServingStatus(service, status)` (names only; item 4, the server start): the
health notifier sets the server's status.
-/
module

public import Proof.google_golang_org.grpc.InvGrpcServer
public import GeneratedProof.google_golang_org.grpc.health
public import Proof.google_golang_org.grpc.InvGrpcHealth

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

/-- `hs.SetServingStatus(service, status)` on grpc's health server returns; `status` is a
`HealthCheckResponse_ServingStatus` (an `int32`: 2026-11-18, it was any `val`, a panic value
included, to which the application unwinds, so the triple could not hold). -/
abbrev health.Server.SetServingStatus.spec : Prop :=
  ∀ (hs : Loc) (service : GoString) (status : w32),
  {{ grpcHealthSrv (GF := GF) hs }}
    (App (App (Val (hs @!! go.GoType.PointerType google_golang_org.grpc.health.Server.ty @!! go!"SetServingStatus"))
      (Val #service)) (Val #status))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
