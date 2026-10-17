/-
grpc-prometheus's `WithServerHandlingTimeHistogram(opts...)` (names only; item 4, the server start):
`getServerMetrics`'s option for `extensive` metrics.
-/
module

public import Proof.google_golang_org.grpc.InvGrpcServer
public import GeneratedProof.github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus

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

/-- `WithServerHandlingTimeHistogram()` (no histogram option) returns one of the provider's own
options (`promSrvMetricsOpt`). -/
abbrev grpc_prometheus.WithServerHandlingTimeHistogram.spec : Prop :=
  {{ (True : IProp GF) }}
    (App (Val (@! github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus.WithServerHandlingTimeHistogram)) (Val #slice.nil))
  {{ (o : GoFunc), RET #o; ⌜promSrvMetricsOpt o⌝ }}

end spec

end EtcdGrove
end Perennial
