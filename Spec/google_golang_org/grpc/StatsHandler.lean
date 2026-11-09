/-
`grpc.StatsHandler` (grpc-go, assumed: `server.go`).

Users: `v3rpc.Server` (`grpc.go:79`, with distributed tracing on).

Why true: the stats handler (etcd's: OpenTelemetry's `otelgrpc`) observes events; it changes nothing the specs model (2e takes it out of scope or proves the handler panic-free).

Changes: from `specs-ref/.../grpc/StatsHandler.lean`.

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
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ True }}
    (App (Val (@! google_golang_org.grpc.StatsHandler)) (Val #h))
  {{ (v : GoInterface), RET #v; srvOptAt v (id) }}

end spec

end Grpc
end EtcdGrove
end Perennial
