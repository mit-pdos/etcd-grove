/-
`grpc.StatsHandler(h)` (item 4, the server start): `v3rpc.Server` installs otelgrpc's
server handler when distributed tracing is on.
-/
module

public import Proof.google_golang_org.grpc.InvGrpcServer
public import Proof.google_golang_org.grpc.InvGrpcStats

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

/-- `grpc.StatsHandler(h)` of a non-nil handler with `grpcStatsHandlerOk` returns an option of the
kind `.stats h`: its closure appends `h` to the stats handlers. -/
abbrev grpc.StatsHandler.spec : Prop :=
  ∀ (h : GoInterface),
  {{ (⌜h ≠ interface.nil ∧ grpcStatsHandlerOk h⌝ : IProp GF) }}
    (App (Val (@! google_golang_org.grpc.StatsHandler)) (Val #h))
  {{ (v : GoInterface), RET #v; grpcSrvOpt v (.stats h) }}

end spec

end EtcdGrove
end Perennial
