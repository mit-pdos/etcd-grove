/-
prometheus's `NewHistogramVec(opts, labelNames)` (names only; metric-vecs, 2026-11-19): a histogram vector with
the variable labels `labelNames` (`vecLabels`), so that the packages' metric vectors have
translated initializers rather than one trust-boundary axiom `<X>_init` each.
-/
module

public import Proof.github_com.prometheus.client_golang.prometheus.Registry
public import Proof.github_com.prometheus.client_golang.prometheus.RegInv
public import Proof.github_com.prometheus.client_golang.prometheus.Labels

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

/-- `prometheus.NewHistogramVec(opts, labelNames)` of label-free options whose `Buckets` slice
`bk` holds strictly increasing finite non-negative bounds (`bucketsOk`), with a valid name, and a
slice `s` of valid, pairwise distinct label names `ls` (`labelNamesOk`) none of which is `le`,
returns a histogram vector with the variable labels `ls` (`vecLabels`: what its
`WithLabelValues` needs, which builds each label combination's histogram with these options,
`newHistogram`, and so panics on bad buckets or a label `le`). The vector keeps both slices (its
descriptor's `variableLabels.names`; the options' `Buckets`, every histogram's `upperBounds`):
their points-to are consumed.(mustreg, 2026-11-20) As a collector
(`*HistogramVec`), it describes one descriptor, of `opts`' fully-qualified name (`collectorName`: what
`MustRegister` needs). -/
abbrev prometheus.NewHistogramVec.spec : Prop :=
  ∀ (o : github_com.prometheus.client_golang.prometheus.HistogramOpts) (ns sub name help : GoString)
    (bk : GoSlice) (bs : List w64) (ls : List GoString) (s : GoSlice) (dq dq' : DFrac),
  prometheus.histOpts o ns sub name help bk →
  prometheus.nameOk (prometheus.fqName ns sub name) →
  prometheus.labelNamesOk ls →
  prometheus.bucketsOk bs →
  go!"le" ∉ ls →
  {{ (s ↦*{dq} ls : IProp GF) ∗ bk ↦*{dq'} bs }}
    (App (App (Val (@! github_com.prometheus.client_golang.prometheus.NewHistogramVec)) (Val #o)) (Val #s))
  {{ (v : Loc), RET #v; ⌜prometheus.vecLabels v ls⌝ ∗
      prometheus.collectorName
        (interface.mk (go.GoType.PointerType github_com.prometheus.client_golang.prometheus.HistogramVec.ty) #v)
        (prometheus.fqName ns sub name) }}

end spec

end EtcdGrove
end Perennial
