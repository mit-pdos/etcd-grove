/-
`HealthCheckResponse_ServingStatus.String()` (grpc's health protocol; item 4, the server start): the
health notifier logs the status's name. Proved over the grpc model's switch (2026-11-27,
`models/grpc/health/grpc_health_v1/health.pb.go`; until then an axiom).
-/
module

public import Proof.google_golang_org.grpc.InvGrpcServer
public import Proof.google_golang_org.grpc.health.grpc_health_v1.Base
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
included, to which the application unwinds, so the triple could not hold) returns a string. Its
package is initialized (2026-11-27, as `SpecPlan`'s: the model's fallback `strconv.Itoa` needs
`strconv`'s initialization, which the package's imports give). -/
abbrev grpc_health_v1.HealthCheckResponse_ServingStatus.String.spec : Prop :=
  ∀ (st : w32),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.health.grpc_health_v1 }}
    (App (App (Val (GoInstruction (MethodResolve google_golang_org.grpc.health.grpc_health_v1.HealthCheckResponse_ServingStatus.ty
      go!"String"))) (Val #st)) (Val #()))
  {{ (s : GoString), RET #s; True }}

end spec

end EtcdGrove
end Perennial
