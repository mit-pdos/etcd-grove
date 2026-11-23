/-
`prometheus.gauge.Sub` (client_golang v1.24.1, `gauge.go`), with its body (prove-ps2-metrics, 2026-11-22).
-/
module

public import Proof.github_com.prometheus.client_golang.prometheus.MetricRep

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.prometheus.client_golang.prometheus.Assumptions]

/-- `g.Sub(x)` is `g.Add(x * -1)`: it returns, for every float64 `x`. -/
abbrev prometheus.gauge.Sub.spec : Prop :=
  ∀ (l : Loc) (x : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus ∗
      prometheus.metric.gaugeCell l }}
    (App (Val (l @!! go.GoType.PointerType github_com.prometheus.client_golang.prometheus.gauge.ty @!!
      go!"Sub")) (Val #x))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
