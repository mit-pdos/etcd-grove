/-
`otelgrpc.NewServerHandler` (`go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc`,
`stats_handler.go`): **assumed** (trust boundary; translated names only).

Why it is true of otelgrpc: the handler's `TagRPC`/`TagConn` start a span over the context they are
given (`ctx` with values added: the tracer provider's, an SDK or no-op one), `HandleRPC`/`HandleConn`
record metrics and span events, under the providers' own locks, from any goroutine; none panics on
grpc's stats values, and none writes memory the program owns. That is grpc's `Grpc.statsOk`.

Users: the server's gRPC server options (`etcdserver/api/v3rpc/grpc.go`, `grpc.StatsHandler(otelgrpc.NewServerHandler(...))` when tracing is on). Requested by grpc-v3rpc (second pass, C-F2: what makes Kubernetes' and the
server's `WithStatsHandler` options `dialOptsOk_neutral`/the server's `StatsHandler.spec` usable).

Margin: the options are read only (their providers assumed otel's own: an SDK or no-op provider, as
every caller in scope passes); what the handler records is not modelled.
-/
module

public import Spec.google_golang_org.grpc.Api
public import Spec.PkgInit.go_opentelemetry_io.contrib.instrumentation.google_golang_org.grpc.otelgrpc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace OtelGrpc

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `NewServerHandler(opts...)`: a stats handler that only observes (`Grpc.statsOk`). -/
def NewServerHandler.spec : Prop :=
  ∀ (opts : GoSlice) (vs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_opentelemetry_io.contrib.instrumentation.google_golang_org.grpc.otelgrpc ∗
      opts ↦*□ vs }}
    (App (Val (@! go_opentelemetry_io.contrib.instrumentation.google_golang_org.grpc.otelgrpc.NewServerHandler)) (Val #opts))
  {{ (h : GoInterface), RET #h; Grpc.statsOk h }}

end spec

end OtelGrpc
end EtcdGrove
end Perennial
