/-
Trust boundary: prometheus's `NewGauge` (an axiom; see
`Spec/github_com/prometheus/client_golang/prometheus/NewGauge.lean`).
-/
module

public import Spec.github_com.prometheus.client_golang.prometheus.NewGauge

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

/-- **Trust boundary**. True of prometheus's Go code (client_golang v1.24.1, `gauge.go`):
`NewGauge(opts)` makes the descriptor `NewDesc(BuildFQName(ns, sub, name), help, nil,
opts.ConstLabels)`, which records an error rather than panicking (here none: the name is non-empty
ASCII, valid UTF-8, and there are no labels), and returns a `*gauge` (its `Describe` sends that
one descriptor) without panicking. The `*gauge` is fresh (`&gauge{desc: desc, labelPairs: ...}`), and
its `valBits` is only ever accessed through `sync/atomic` (`Set`, `Add`, `Write`), hence the invariant
of `metric.isGauge`. (prove-ps2-metrics, 2026-11-22: until then this axiom claimed `Inc`'s, `Dec`'s,
`Add`'s and `Set`'s triples, which are now proved over their bodies.) -/
axiom prometheus.NewGauge.wp_proof : prometheus.NewGauge.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
