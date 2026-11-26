/-
grpc-prometheus's `NewServerMetrics(opts...)` (names only; item 4, the server start).
-/
module

public import Proof.google_golang_org.grpc.InvGrpcServer
public import GeneratedProof.github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus
public import Proof.github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus.Defs
public import Proof.google_golang_org.grpc.InvGrpcProm

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
histogram is made with prometheus's default buckets) returns server metrics (`promSrvMetrics`).
(prom-registry, route (b), 2026-11-22) As a collector (`Describe`, which prometheus's `Register` calls)
they describe (`describes`) the four counter vectors' descriptors and, if an option enabled the histogram
(any option does: `promSrvMetricsOpt`), the histogram vector's, in that order (providers/prometheus v1.1.0,
`server_metrics.go:89-97`: `ServerMetrics.Describe` calls each vector's `Describe`, which sends its one
`*Desc`, `MetricVec.Describe`), each read-only for good, of the names `srvNames`, label-free (no const
labels: no counter or histogram option and no context label sets any; client_golang v1.24.1, `desc.go`
`V2.NewDesc`: the ID hashes the name and the const label values only) and valid (`srvDescsOk`). -/
abbrev grpc_prometheus.NewServerMetrics.spec : Prop :=
  ∀ (sl : GoSlice) (os : List GoFunc),
  {{ (sl ↦*□ os ∗ [∗list] o ∈ os, promSrvMetricsOpt o : IProp GF) }}
    (App (Val (@! github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus.NewServerMetrics)) (Val #sl))
  {{ (m : Loc), RET #m; ⌜m ≠ null⌝ ∗ promSrvMetrics m ∗
      ∃ (ps : List Loc) (ds : List github_com.prometheus.client_golang.prometheus.Desc),
        prometheus.describes
          (interface.mk (go.GoType.PointerType github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus.ServerMetrics.ty) #m)
          ps ∗
        ([∗list] p;d ∈ ps;ds, p ↦□ d) ∗ ⌜grpc_prometheus.srvDescsOk (!os.isEmpty) ds⌝ }}

end spec

end EtcdGrove
end Perennial
