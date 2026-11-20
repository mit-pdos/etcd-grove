/-
prometheus's `NewGaugeFunc(opts, function)` (names only): returns a gauge-func collector, without
calling `function`.
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

/-- `prometheus.NewGaugeFunc(opts, function)` of label-free options (`GaugeOpts` is `Opts`, as
`CounterOpts`: `counterOpts`) returns a non-nil `GaugeFunc` and does not call `function` (any
function value). Nothing about the result's methods: its users here only register it, in an
untranslated `init` (`initFuncsOk`). -/
abbrev prometheus.NewGaugeFunc.spec : Prop :=
  ∀ (o : github_com.prometheus.client_golang.prometheus.GaugeOpts) (ns sub name help : GoString)
    (f : GoFunc),
  prometheus.counterOpts o ns sub name help →
  {{ (True : IProp GF) }}
    (App (App (Val (@! github_com.prometheus.client_golang.prometheus.NewGaugeFunc)) (Val #o)) (Val #f))
  {{ (g : GoInterfaceOk), RET #(GoInterface.ok g); True }}

end spec

end EtcdGrove
end Perennial
