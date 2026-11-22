/-
Proof of `Spec/github_com/prometheus/client_golang/prometheus/gauge__Inc.lean`, over the real body
(prove-ps2-metrics, 2026-11-22).
-/
module

public import Spec.github_com.prometheus.client_golang.prometheus.gauge__Inc
public import Spec.github_com.prometheus.client_golang.prometheus.gauge__Add
public import Perennial.Golang.Theory.Float

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode prometheus.metric

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.prometheus.client_golang.prometheus.Assumptions]

theorem prometheus.gauge.Inc.wp_proof (wp_Add : prometheus.gauge.Add.spec (GF := GF) (hG := hG)) :
    prometheus.gauge.Inc.spec (GF := GF) (hG := hG) := by
  intro l
  wp_start as #Hcell
  wp_auto

  wp_apply wp_Add $$ [$Hcell]
  iapply HΦ
  try itrivial

end proof

end EtcdGrove
end Perennial
