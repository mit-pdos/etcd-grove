/-
Trust boundary: grpc-prometheus's `ServerMetrics.InitializeMetrics` (an axiom; see `Spec/github_com/grpc_ecosystem/go_grpc_middleware/providers/prometheus/ServerMetrics__InitializeMetrics.lean`).
-/
module

public import Spec.github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus.ServerMetrics__InitializeMetrics

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

/-- **Trust boundary** (item 4, the server start): it calls `gs.GetServiceInfo()` (which reads the
server's registered services under its mutex, changing nothing) and initializes, for each method,
the metrics' label values (counters at zero). -/
axiom grpc_prometheus.ServerMetrics.InitializeMetrics.wp_proof : grpc_prometheus.ServerMetrics.InitializeMetrics.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
