/-
prometheus's `ExponentialBuckets(start, factor, count)` (names only), for `factor = 2`.
-/
module

public import Proof.github_com.prometheus.client_golang.prometheus.Registry

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

/-- `prometheus.ExponentialBuckets(start, 2, count)` of a positive normal `start` and a
`count ≥ 1` whose last bucket is finite (`expBucketsArgsOk`), with `factor` the float64 `2.0`
(`float64Two`), returns a new slice of the `count`
buckets `start * 2^i` (`expBuckets`, exact). -/
abbrev prometheus.ExponentialBuckets.spec : Prop :=
  ∀ (start factor count : w64),
  factor = prometheus.float64Two →
  prometheus.expBucketsArgsOk start count →
  {{ (True : IProp GF) }}
    (App (App (App (Val (@! github_com.prometheus.client_golang.prometheus.ExponentialBuckets))
      (Val #start)) (Val #factor)) (Val #count))
  {{ (s : GoSlice), RET #s; s ↦* prometheus.expBuckets start (sint.Z count).toNat }}

end spec

end EtcdGrove
end Perennial
