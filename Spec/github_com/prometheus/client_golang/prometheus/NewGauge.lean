/-
prometheus's `NewGauge(opts)` (names only): a gauge whose one descriptor is named
`BuildFQName(opts.Namespace, opts.Subsystem, opts.Name)`.
-/
module

public import Proof.github_com.prometheus.client_golang.prometheus.Registry
public import Proof.github_com.prometheus.client_golang.prometheus.RegInv
public import Proof.github_com.prometheus.client_golang.prometheus.Metric
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `prometheus.NewGauge(opts)` of label-free options (`GaugeOpts` is `Opts`, as `CounterOpts`:
`counterOpts`) with a valid name returns a gauge (`metric.isGauge`: a `*gauge` whose value cell is in an
invariant; its methods' specs are proved, and `metric.gaugeSpec_of_isGauge`/`gaugeSetSpec_of_isGauge`
recover `metric.gaugeSpec` and `metric.gaugeSetSpec`) that describes one descriptor, of `opts`'
fully-qualified name. (prove-ps2-metrics, 2026-11-22: until then the post claimed those two
itself.) -/
abbrev prometheus.NewGauge.spec : Prop :=
  ∀ (o : github_com.prometheus.client_golang.prometheus.GaugeOpts) (ns sub name help : GoString),
  prometheus.counterOpts o ns sub name help →
  prometheus.nameOk (prometheus.fqName ns sub name) →
  {{ (True : IProp GF) }}
    (App (Val (@! github_com.prometheus.client_golang.prometheus.NewGauge)) (Val #o))
  {{ (g : GoInterfaceOk), RET #(GoInterface.ok g);
      prometheus.metric.isGauge g ∗
      prometheus.collectorName g (prometheus.fqName ns sub name) }}

end spec

end EtcdGrove
end Perennial
