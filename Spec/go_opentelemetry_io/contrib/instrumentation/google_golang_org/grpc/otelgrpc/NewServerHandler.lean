/-
otelgrpc's `NewServerHandler(opts...)` (names only; item 4, the server start): `v3rpc.Server`'s
stats handler when distributed tracing is on.
-/
module

public import Proof.google_golang_org.grpc.InvGrpcServer
public import GeneratedProof.go_opentelemetry_io.contrib.instrumentation.google_golang_org.grpc.otelgrpc

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

/-- `otelgrpc.NewServerHandler(opts...)` (the options read-only) returns a stats handler with
`grpcStatsHandlerOk`. -/
abbrev otelgrpc.NewServerHandler.spec : Prop :=
  ∀ (sl : GoSlice) (os : List GoInterface),
  {{ (sl ↦*□ os : IProp GF) }}
    (App (Val (@! go_opentelemetry_io.contrib.instrumentation.google_golang_org.grpc.otelgrpc.NewServerHandler))
      (Val #sl))
  {{ (h : GoInterface), RET #h; ⌜grpcStatsHandlerOk h⌝ }}

end spec

end EtcdGrove
end Perennial
