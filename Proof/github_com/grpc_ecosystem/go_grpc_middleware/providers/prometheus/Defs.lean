/-
grpc-prometheus's server-metrics options (`ServerMetricsOption`, `func(*serverMetricsConfig)`), as
`NewServerMetrics` takes them: `promSrvMetricsOpt o` (persistent), `o` sets the config's histogram
fields as `WithServerHandlingTimeHistogram()` does (providers/prometheus v1.1.0,
`server_options.go:42-47`: `histogramOpts` to its (empty) options, `enableHistogram` to `true`) and
touches nothing else. Lean-first (prove-metrics3, 2026-11-21: until then an opaque `Prop`, a
trust-boundary axiom of `InvGrpcServer.lean`).
-/
module

public import GeneratedProof.github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus
public import Perennial.Proof.ProofPrelude

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`o` is one of grpc-prometheus's own server-metrics options** (persistent; see the file
header): applied to a config `c`, it sets `c.histogramOpts` to the empty options and
`c.enableHistogram` to `true`, and returns. -/
def promSrvMetricsOpt (o : GoFunc) : IProp GF :=
  iprop(□ ∀ (c : Loc) (ho : GoSlice) (eh : Bool),
    {{ c.[serverMetricsConfig, go!"histogramOpts"] ↦ ho ∗
        c.[serverMetricsConfig, go!"enableHistogram"] ↦ eh }}
      (App (Val #o) (Val #c))
    {{ RET #(); c.[serverMetricsConfig, go!"histogramOpts"] ↦ slice.nil ∗
        c.[serverMetricsConfig, go!"enableHistogram"] ↦ true }})

instance promSrvMetricsOpt_persistent (o : GoFunc) :
    Persistent (promSrvMetricsOpt (GF := GF) o) := by
  unfold promSrvMetricsOpt; infer_instance

end defs

end EtcdGrove
end Perennial
