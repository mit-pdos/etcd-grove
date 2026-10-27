/-
Trust boundary: grpc-prometheus's `ServerMetrics.UnaryServerInterceptor` (an axiom; see `Spec/github_com/grpc_ecosystem/go_grpc_middleware/providers/prometheus/ServerMetrics__UnaryServerInterceptor.lean`).
-/
module

public import Spec.github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus.ServerMetrics__UnaryServerInterceptor

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

/-- **Trust boundary** (item 4, the server start): the interceptor
(`interceptors.UnaryServerInterceptor` over the metrics' reporter) records the call's start, calls
`handler(ctx, req)` once with the same context and request, records its end (counters, histograms:
safe from any goroutine) and returns the handler's result unchanged. What `etcd_kv_served` assumed
of it until item 4. -/
axiom grpc_prometheus.ServerMetrics.UnaryServerInterceptor.wp_proof : grpc_prometheus.ServerMetrics.UnaryServerInterceptor.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
