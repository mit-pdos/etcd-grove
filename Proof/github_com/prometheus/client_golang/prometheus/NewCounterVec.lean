/-
Trust boundary: prometheus's `NewCounterVec` (an axiom; see
`Spec/github_com/prometheus/client_golang/prometheus/NewCounterVec.lean`).
-/
module

public import Spec.github_com.prometheus.client_golang.prometheus.NewCounterVec

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
v1.24.1, `counter.go`, `desc.go`, `vec.go`): `NewCounterVec(opts, labelNames)` calls
`V2.NewCounterVec` with `VariableLabels: UnconstrainedLabels(labelNames)`, which makes the
descriptor `V2.NewDesc(BuildFQName(ns, sub, name), help, opts.VariableLabels, opts.ConstLabels,
WithUnit(opts.Unit))`: its `variableLabels` is `compile()`, a `*compiledLabels` whose `names` is
the slice `labelNames` itself (no copy: the slice is kept), and it records an error rather than
panicking on an invalid name (`nameOk` excludes it), an invalid label name (`checkLabelName`;
`labelNameOk` excludes it) or duplicate label names (`labelNamesOk`), with no const labels. It
then returns `&CounterVec{MetricVec: NewMetricVec(desc, newMetric)}` (a fresh pointer; nothing
panics). Its `WithLabelValues(lvs...)` (`GetMetricWithLabelValues`) panics only on an error of
`validateLabelValues` (a wrong count, a value not valid UTF-8; uncurried, unconstrained), and the
closure `newMetric` only on a wrong count: what `CounterVec.WithLabelValues.spec` takes from
`vecLabels` and `labelValuesOk`. (mustreg, 2026-11-20) Its post's `collectorName`: the
result, as a `Collector` (`*CounterVec`), describes one descriptor, `desc` (`MetricVec.Describe`,
`vec.go:124`, is `metricMap.Describe`, which sends `m.desc` alone), named `BuildFQName(ns, sub,
name)` (`fqName`), valid (as above), without const labels (`counterOpts`/`histOpts`: `ConstLabels`
nil); its variable labels enter `desc.dimHash`, not `desc.id` (`NewDesc`, `desc.go`). -/
axiom prometheus.NewCounterVec.wp_proof : prometheus.NewCounterVec.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
