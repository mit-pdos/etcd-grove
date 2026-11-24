/-
prometheus's `NewHistogram(opts)` (names only): a histogram whose one descriptor is named
`BuildFQName(opts.Namespace, opts.Subsystem, opts.Name)`, over increasing buckets.
-/
module

public import Proof.github_com.prometheus.client_golang.prometheus.Registry
public import Proof.github_com.prometheus.client_golang.prometheus.RegInv
public import Proof.github_com.prometheus.client_golang.prometheus.Metric

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

/-- `prometheus.NewHistogram(opts)` of label-free options whose `Buckets` slice `s` holds strictly
increasing finite non-negative bounds (`bucketsOk`), with a valid name, returns a histogram
(`metric.histSpec`: `Observe` of any value returns) that describes one descriptor, of `opts`'
fully-qualified name. The histogram keeps `s` as its upper bounds (`upperBounds: opts.Buckets`,
read by every `Observe`): the slice's points-to is consumed. -/
abbrev prometheus.NewHistogram.spec : Prop :=
  ∀ (o : github_com.prometheus.client_golang.prometheus.HistogramOpts) (ns sub name help : GoString)
    (s : GoSlice) (bs : List w64) (dq : DFrac),
  prometheus.histOpts o ns sub name help s →
  prometheus.bucketsOk bs →
  prometheus.nameOk (prometheus.fqName ns sub name) →
  {{ (s ↦*{dq} bs : IProp GF) }}
    (App (Val (@! github_com.prometheus.client_golang.prometheus.NewHistogram)) (Val #o))
  {{ (h : GoInterfaceOk), RET #(GoInterface.ok h);
      prometheus.metric.histSpec h ∗
      prometheus.collectorName h (prometheus.fqName ns sub name) }}

end spec

end EtcdGrove
end Perennial
