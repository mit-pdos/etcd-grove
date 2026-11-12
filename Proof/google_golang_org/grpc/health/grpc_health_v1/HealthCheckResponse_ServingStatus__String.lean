/-
Trust boundary: `grpc_health_v1.HealthCheckResponse_ServingStatus.String` (an axiom; see `Spec/google_golang_org/grpc/health/grpc_health_v1/HealthCheckResponse_ServingStatus__String.lean`).
-/
module

public import Spec.google_golang_org.grpc.health.grpc_health_v1.HealthCheckResponse_ServingStatus__String

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Trust boundary** (item 4, the server start): the generated `String` of a protobuf enum returns
`protoimpl.X.EnumStringOf(x.Descriptor(), protoreflect.EnumNumber(x))`: the value's name, or its
number formatted; it reads only the package's immutable descriptors. -/
axiom grpc_health_v1.HealthCheckResponse_ServingStatus.String.wp_proof : grpc_health_v1.HealthCheckResponse_ServingStatus.String.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
