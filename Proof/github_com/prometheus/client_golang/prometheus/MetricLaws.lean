/-
`NewGauge`'s method claims (`metric.gaugeSpec`, `metric.gaugeSetSpec`, `Metric.lean`) from the
representation it returns (`metric.isGauge`, `MetricRep.lean`) and the methods' specs, which are proved over the real bodies (prove-ps2-metrics,
2026-11-22: until then `NewGauge`'s axiom claimed the methods' triples themselves). Each law
takes the methods' specs as hypotheses (the package initializers apply it with the linked results).
-/
module

public import Proof.github_com.prometheus.client_golang.prometheus.Metric
public import Spec.github_com.prometheus.client_golang.prometheus.gauge__Set
public import Spec.github_com.prometheus.client_golang.prometheus.gauge__Add
public import Spec.github_com.prometheus.client_golang.prometheus.gauge__Sub
public import Spec.github_com.prometheus.client_golang.prometheus.gauge__Inc
public import Spec.github_com.prometheus.client_golang.prometheus.gauge__Dec
public import Perennial.Golang.Theory.Float

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace prometheus.metric

open Iris Iris.BI Iris.ProofMode

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.prometheus.client_golang.prometheus.Assumptions]

theorem gaugeSpec_of_isGauge
    (wp_Inc : prometheus.gauge.Inc.spec (GF := GF) (hG := hG))
    (wp_Dec : prometheus.gauge.Dec.spec (GF := GF) (hG := hG))
    (wp_Add : prometheus.gauge.Add.spec (GF := GF) (hG := hG)) (g : GoInterfaceOk) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus -∗
      isGauge g -∗ gaugeSpec g := by
  iintro #Hinit #Hg
  iunfold isGauge at Hg
  icases Hg with ⟨%l, %Heq, #Hc⟩
  subst Heq
  iunfold gaugeSpec
  isplitr
  · imodintro
    iintro %Φ
    imodintro
    iintro _ HΦ
    dsimp only
    wp_apply wp_Inc $$ [$Hc]
    iapply HΦ
    try itrivial
  isplitr
  · imodintro
    iintro %Φ
    imodintro
    iintro _ HΦ
    dsimp only
    wp_apply wp_Dec $$ [$Hc]
    iapply HΦ
    try itrivial
  · imodintro
    iintro %x %Φ
    imodintro
    iintro _ HΦ
    dsimp only
    wp_apply wp_Add $$ [$Hc]
    iapply HΦ
    try itrivial

theorem gaugeSetSpec_of_isGauge
    (wp_Set : prometheus.gauge.Set.spec (GF := GF) (hG := hG)) (g : GoInterfaceOk) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus -∗
      isGauge g -∗ gaugeSetSpec g := by
  iintro #Hinit #Hg
  iunfold isGauge at Hg
  icases Hg with ⟨%l, %Heq, #Hc⟩
  subst Heq
  iunfold gaugeSetSpec
  imodintro
  iintro %x %Φ
  imodintro
  iintro _ HΦ
  dsimp only
  wp_apply wp_Set $$ [$Hc]
  iapply HΦ
  try itrivial

end laws

end prometheus.metric
end EtcdGrove
end Perennial
