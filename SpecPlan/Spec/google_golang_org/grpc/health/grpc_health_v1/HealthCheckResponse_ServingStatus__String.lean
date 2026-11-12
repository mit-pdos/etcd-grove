/-
`HealthCheckResponse_ServingStatus.String()` (grpc-go, assumed: the generated enum stringer of
`health/grpc_health_v1/health.pb.go`, `protoimpl.X.EnumStringOf`).

Users: `v3rpc.healthNotifier.startServe`/`stopServe` (`server/etcdserver/api/v3rpc/health.go:66,75`:
`healthpb.HealthCheckResponse_SERVING.String()` logged).

Why true: it looks the value up in the enum's descriptor (built at package initialization) and
returns its name, else the number in decimal; it reads only its receiver, a value.

Changes: verify-round: restored (A6 completeness F6: dropped from the old tree,
`specs-ref/Spec/google_golang_org/grpc/health/grpc_health_v1/HealthCheckResponse_ServingStatus__String.lean`),
over the package's `isPkgInit`.
Margin: the string is the value's name; the spec says only that one is returned (its users log it).
-/
module

public import SpecPlan.Spec.google_golang_org.grpc.Api
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

/-- `st.String()` of a serving status: some string. -/
def grpc_health_v1.HealthCheckResponse_ServingStatus.String.spec : Prop :=
  ∀ (st : w32),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.health.grpc_health_v1 }}
    (App (Val (st @!! google_golang_org.grpc.health.grpc_health_v1.HealthCheckResponse_ServingStatus.ty
      @!! go!"String")) (Val #()))
  {{ (s : GoString), RET #s; True }}

end spec

end Grpc
end EtcdGrove
end Perennial
