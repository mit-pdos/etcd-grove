/-
Trust boundary: grpc-prometheus's `WithServerHandlingTimeHistogram` (an axiom; see `Spec/github_com/grpc_ecosystem/go_grpc_middleware/providers/prometheus/WithServerHandlingTimeHistogram.lean`).
-/
module

public import Spec.github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus.WithServerHandlingTimeHistogram

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

/-- **Trust boundary** (item 4, the server start): it returns a closure that, applied by
`NewServerMetrics`, sets the configuration's handling-time histogram (with no option: the default
buckets). -/
axiom grpc_prometheus.WithServerHandlingTimeHistogram.wp_proof : grpc_prometheus.WithServerHandlingTimeHistogram.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
