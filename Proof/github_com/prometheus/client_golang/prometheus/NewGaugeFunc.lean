/-
Trust boundary: prometheus's `NewGaugeFunc` (an axiom; see
`Spec/github_com/prometheus/client_golang/prometheus/NewGaugeFunc.lean`).
-/
module

public import Spec.github_com.prometheus.client_golang.prometheus.NewGaugeFunc

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

/-- **Trust boundary**. True of prometheus's Go code (client_golang v1.24.1, `gauge.go:306`):
`NewGaugeFunc(opts, function)` is `newValueFunc(V2.NewDesc(BuildFQName(ns, sub, name), help,
UnconstrainedLabels(nil), opts.ConstLabels, WithUnit(opts.Unit)), GaugeValue, function)`. `NewDesc`
records an invalid name or label in the descriptor's `err` rather than panicking (here there are no
labels: `ConstLabels` is nil), and `newValueFunc` (`value.go:79`) allocates a `*valueFunc` holding
`function` (not called), `MakeLabelPairs(desc, nil)` (no labels: `nil`) and runs
`selfCollector.init`, a field store: a non-nil result, no panic. -/
axiom prometheus.NewGaugeFunc.wp_proof : prometheus.NewGaugeFunc.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
