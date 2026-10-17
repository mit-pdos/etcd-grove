/-
Trust boundary: grpc-prometheus's `NewServerMetrics` (an axiom; see `Spec/github_com/grpc_ecosystem/go_grpc_middleware/providers/prometheus/NewServerMetrics.lean`).
-/
module

public import Spec.github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus.NewServerMetrics

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Trust boundary** (item 4, the server start): `NewServerMetrics` applies the options to a
configuration (the provider's options only set fields of it) and allocates the counters and
histograms: a non-nil `*ServerMetrics`, whose methods are safe from any goroutine (prometheus's
vectors lock internally). -/
axiom grpc_prometheus.NewServerMetrics.wp_proof : grpc_prometheus.NewServerMetrics.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
