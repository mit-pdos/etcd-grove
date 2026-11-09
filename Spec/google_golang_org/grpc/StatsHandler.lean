/-
`grpc.StatsHandler` (grpc-go, assumed: `server.go`).

Users: `v3rpc.Server` (`grpc.go:79`, with distributed tracing on).

Why true: the stats handler (etcd's: OpenTelemetry's `otelgrpc`) observes events; an observing one
(`statsOk`: its methods return, writing nothing the specs own) changes nothing the specs model.

Changes: from `specs-ref/.../grpc/StatsHandler.lean`.
verify-round (A6 second tier, with the client's `WithStatsHandler`): premise `statsOk h` (grpc calls
the handler on every RPC: a panicking one would break the claim); otelgrpc's `statsOk` is its
owner's (requested of client-core, the otel owner).

Margin: none.
-/
module

public import Spec.google_golang_org.grpc.Api

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

/-- `grpc.StatsHandler(...)`: a server option acting as shown. -/
def StatsHandler.spec : Prop :=
  ∀ (h : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ statsOk h }}
    (App (Val (@! google_golang_org.grpc.StatsHandler)) (Val #h))
  {{ (v : GoInterface), RET #v; srvOptAt v (id) }}

end spec

end Grpc
end EtcdGrove
end Perennial
