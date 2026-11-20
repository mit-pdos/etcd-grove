/-
Trust boundary: prometheus's `NewHistogram` (an axiom; see
`Spec/github_com/prometheus/client_golang/prometheus/NewHistogram.lean`).
-/
module

public import Spec.github_com.prometheus.client_golang.prometheus.NewHistogram

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

/-- **Trust boundary**. True of prometheus's Go code (client_golang v1.24.1, `histogram.go`):
`NewHistogram(opts)` makes the descriptor `NewDesc(BuildFQName(ns, sub, name), help, nil,
opts.ConstLabels)` (an error recorded, not a panic; here none) and calls `newHistogram(desc, opts)`,
which panics only on a label named `le` (none: no labels) or on bucket upper bounds that are not
strictly increasing (`bucketsOk` excludes it: finite non-negative float64s, whose order is their
bits' order); with `NativeHistogramBucketFactor` zero, native histograms are off and no other
option is read for a check. It keeps `opts.Buckets` as `upperBounds` (no copy; a trailing `+Inf` is
cut off by reslicing). Its `Observe(v)` finds `v`'s bucket (`sort.SearchFloat64s`) and adds to its
counts atomically: it does not panic, for any float64. -/
axiom prometheus.NewHistogram.wp_proof : prometheus.NewHistogram.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
