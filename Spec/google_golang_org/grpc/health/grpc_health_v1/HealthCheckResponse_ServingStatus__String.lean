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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `st.String()` of a serving status returns a string. -/
abbrev grpc_health_v1.HealthCheckResponse_ServingStatus.String.spec : Prop :=
  ∀ (st : val),
  {{ (True : IProp GF) }}
    (App (Val #(methods google_golang_org.grpc.health.grpc_health_v1.HealthCheckResponse_ServingStatus.ty go!"String" st)) (Val #()))
  {{ (s : GoString), RET #s; True }}

end spec

end EtcdGrove
end Perennial
