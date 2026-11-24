/-
prometheus's `NewGaugeFunc(opts, function)` (names only): returns a gauge-func collector, without
calling `function`.
-/
module

public import Proof.github_com.prometheus.client_golang.prometheus.Registry
public import Proof.github_com.prometheus.client_golang.prometheus.RegInv

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

/-- `prometheus.NewGaugeFunc(opts, function)` of label-free options (`GaugeOpts` is `Opts`, as
`CounterOpts`: `counterOpts`) returns a non-nil `GaugeFunc` and does not call `function` (any
function value). Nothing about the result's methods: its users here only register it
(`MustRegister`, in their translated `init`). (etcdstorage, 2026-11-20) If the fully-qualified name
is valid, the result describes one descriptor, of that name (`collectorName`): client_golang v1.24.1,
`gauge.go:306` `NewGaugeFunc` is `newValueFunc(V2.NewDesc(BuildFQName(ns, sub, name), help,
UnconstrainedLabels(nil), ConstLabels, WithUnit(Unit)), GaugeValue, function)` (`value.go:79`: the
`valueFunc` is its own `selfCollector`), whose `Describe` sends its one `desc` (`collector.go:113`);
with no labels and no const labels the descriptor is `collectorName`'s, as `NewGauge`'s. -/
abbrev prometheus.NewGaugeFunc.spec : Prop :=
  ∀ (o : github_com.prometheus.client_golang.prometheus.GaugeOpts) (ns sub name help : GoString)
    (f : GoFunc),
  prometheus.counterOpts o ns sub name help →
  {{ (True : IProp GF) }}
    (App (App (Val (@! github_com.prometheus.client_golang.prometheus.NewGaugeFunc)) (Val #o)) (Val #f))
  {{ (g : GoInterfaceOk), RET #(GoInterface.ok g);
      (⌜prometheus.nameOk (prometheus.fqName ns sub name)⌝ →
        prometheus.collectorName g (prometheus.fqName ns sub name)) }}

end spec

end EtcdGrove
end Perennial
