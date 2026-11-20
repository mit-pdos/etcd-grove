/-
Trust boundary: prometheus's `ExponentialBuckets` (an axiom; see
`Spec/github_com/prometheus/client_golang/prometheus/ExponentialBuckets.lean`).
-/
module

public import Spec.github_com.prometheus.client_golang.prometheus.ExponentialBuckets

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
`ExponentialBuckets(start, factor, count)` panics only if `count < 1`, `start <= 0` or
`factor <= 1` (none here: `count ≥ 1`, `start` positive, `factor = 2`), and otherwise returns
`make([]float64, count)` filled by `buckets[i] = start; start *= factor`. With `factor = 2` and
`start` normal, each product of a normal float64 whose result stays normal (`expBucketsArgsOk`: up
to the last bucket) is exact, `2^52` added to the bits (the multiplication after the last bucket may
overflow to `+Inf`, unused). -/
axiom prometheus.ExponentialBuckets.wp_proof : prometheus.ExponentialBuckets.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
