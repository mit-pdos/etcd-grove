/-
Trust boundary: prometheus's `NewHistogramVec` (an axiom; see
`Spec/github_com/prometheus/client_golang/prometheus/NewHistogramVec.lean`).
-/
module

public import Spec.github_com.prometheus.client_golang.prometheus.NewHistogramVec

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
v1.24.1, `histogram.go`, `desc.go`, `vec.go`): `NewHistogramVec(opts, labelNames)` calls
`V2.NewHistogramVec` with `VariableLabels: UnconstrainedLabels(labelNames)`, which makes the
descriptor as `NewCounterVec` does (the slice `labelNames` kept; an error recorded, not a panic,
on an invalid name or label name or duplicate label names, which the premises exclude) and returns
`&HistogramVec{MetricVec: NewMetricVec(desc, func(lvs...) { return newHistogram(desc,
opts.HistogramOpts, lvs...) })}` (a fresh pointer; nothing panics: no histogram is built yet). The
closure, run by `WithLabelValues` for a new label combination, panics on a wrong count, on a
variable label named `le` (excluded: `go!"le" ∉ ls`; no const labels) or on bucket upper bounds
not strictly increasing (excluded: `bucketsOk`; `NativeHistogramBucketFactor` zero, so no other
option is checked), and keeps `opts.Buckets` as the histogram's `upperBounds` (the options are
captured by the closure: the bucket slice is kept). `WithLabelValues` otherwise panics only on an
error of `validateLabelValues`: what `HistogramVec.WithLabelValues.spec` takes from `vecLabels`. -/
axiom prometheus.NewHistogramVec.wp_proof : prometheus.NewHistogramVec.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
