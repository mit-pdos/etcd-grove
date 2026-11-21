/-
grpc-prometheus's `NewServerMetrics(opts...)` (names only; item 4, the server start).
-/
module

public import Proof.google_golang_org.grpc.InvGrpcServer
public import GeneratedProof.github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus
public import Proof.github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus.Defs

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

/-- `NewServerMetrics(opts...)` with options (read-only) that set the config's histogram fields as
the provider's `WithServerHandlingTimeHistogram()` does (`promSrvMetricsOpt`, defined 2026-11-21:
`config.apply(opts)` runs each on the local `config`, whose histogram options are then empty, so the
histogram is made with prometheus's default buckets) returns server metrics (`promSrvMetrics`). -/
abbrev grpc_prometheus.NewServerMetrics.spec : Prop :=
  ∀ (sl : GoSlice) (os : List GoFunc),
  {{ (sl ↦*□ os ∗ [∗list] o ∈ os, promSrvMetricsOpt o : IProp GF) }}
    (App (Val (@! github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus.NewServerMetrics)) (Val #sl))
  {{ (m : Loc), RET #m; ⌜m ≠ null⌝ ∗ promSrvMetrics m }}

end spec

end EtcdGrove
end Perennial
