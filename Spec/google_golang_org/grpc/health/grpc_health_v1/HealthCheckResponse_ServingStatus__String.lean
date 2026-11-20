/-
`HealthCheckResponse_ServingStatus.String()` (grpc's health protocol, names only; item 4, the server
start): the health notifier logs the status's name.
-/
module

public import Proof.google_golang_org.grpc.InvGrpcServer
public import GeneratedProof.google_golang_org.grpc.health.grpc_health_v1

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

/-- `st.String()` of a serving status (an `int32`: 2026-11-18, it was any `val`, a panic value
included, to which the application unwinds, so the triple could not hold) returns a string. -/
abbrev grpc_health_v1.HealthCheckResponse_ServingStatus.String.spec : Prop :=
  ∀ (st : w32),
  {{ (True : IProp GF) }}
    (App (App (Val (GoInstruction (MethodResolve google_golang_org.grpc.health.grpc_health_v1.HealthCheckResponse_ServingStatus.ty
      go!"String"))) (Val #st)) (Val #()))
  {{ (s : GoString), RET #s; True }}

end spec

end EtcdGrove
end Perennial
