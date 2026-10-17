/-
Trust boundary: grpc-prometheus's `ServerMetrics.StreamServerInterceptor` (an axiom; see `Spec/github_com/grpc_ecosystem/go_grpc_middleware/providers/prometheus/ServerMetrics__StreamServerInterceptor.lean`).
-/
module

public import Spec.github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus.ServerMetrics__StreamServerInterceptor

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

/-- **Trust boundary** (item 4, the server start): the interceptor records the stream's start, calls
`handler(srv, ss')` once, `ss'` the stream wrapped in a counting `monitoredServerStream` (its
`RecvMsg`/`SendMsg` are the stream's, counted; its context the stream's), records the end and
returns the handler's error unchanged. What `etcd_watch_served_chain` assumed of it until item 4. -/
axiom grpc_prometheus.ServerMetrics.StreamServerInterceptor.wp_proof : grpc_prometheus.ServerMetrics.StreamServerInterceptor.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
