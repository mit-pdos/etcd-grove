/-
`grpc.StatsHandler(h)` (names only; item 4, the server start): `v3rpc.Server` installs otelgrpc's
server handler when distributed tracing is on.
-/
module

public import Proof.google_golang_org.grpc.InvGrpcServer

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

/-- `grpc.StatsHandler(h)` of a handler with `grpcStatsHandlerOk` returns a neutral option. -/
abbrev grpc.StatsHandler.spec : Prop :=
  ∀ (h : GoInterface),
  {{ (⌜grpcStatsHandlerOk h⌝ : IProp GF) }}
    (App (Val (@! google_golang_org.grpc.StatsHandler)) (Val #h))
  {{ (v : GoInterface), RET #v; ⌜grpcSrvOpt v .neutral⌝ }}

end spec

end EtcdGrove
end Perennial
