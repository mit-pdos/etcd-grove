/-
Trust boundary: prometheus's `NewGaugeVec` (an axiom; see
`Spec/github_com/prometheus/client_golang/prometheus/NewGaugeVec.lean`).
-/
module

public import Spec.github_com.prometheus.client_golang.prometheus.NewGaugeVec

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

/-- **Trust boundary** (metric-vecs, 2026-11-19). True of prometheus's Go code (client_golang
v1.24.1, `gauge.go`, `desc.go`, `vec.go`): `NewGaugeVec(opts, labelNames)` calls `V2.NewGaugeVec`
with `VariableLabels: UnconstrainedLabels(labelNames)`, which makes the descriptor as
`NewCounterVec` does (the slice `labelNames` kept as its `variableLabels.names`; an error recorded,
not a panic, on an invalid name or label name or duplicate label names, which the premises
exclude) and returns `&GaugeVec{MetricVec: NewMetricVec(desc, newMetric)}` (a fresh pointer;
nothing panics). Its `WithLabelValues` panics only on an error of `validateLabelValues`, its `With`
only on one of `validateValuesInLabels`/`hashLabels` (the map's keys not the label names, a value
not valid UTF-8), the closure only on a wrong count: what `GaugeVec.WithLabelValues.spec` and
`GaugeVec.With.spec` take from `vecLabels`. (mustreg, 2026-11-20) Its post's `collectorName`: the
result, as a `Collector` (`*GaugeVec`), describes one descriptor, `desc` (`MetricVec.Describe`,
`vec.go:124`, is `metricMap.Describe`, which sends `m.desc` alone), named `BuildFQName(ns, sub,
name)` (`fqName`), valid (as above), without const labels (`counterOpts`/`histOpts`: `ConstLabels`
nil); its variable labels enter `desc.dimHash`, not `desc.id` (`NewDesc`, `desc.go`). -/
axiom prometheus.NewGaugeVec.wp_proof : prometheus.NewGaugeVec.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
