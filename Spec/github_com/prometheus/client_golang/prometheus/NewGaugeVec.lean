/-
prometheus's `NewGaugeVec(opts, labelNames)` (names only; metric-vecs, 2026-11-19): a gauge vector with
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

/-- `prometheus.NewGaugeVec(opts, labelNames)` of label-free options (`GaugeOpts` is `Opts`, as
`CounterOpts`: `counterOpts`) with a valid name, and a slice `s` of valid, pairwise distinct label
names `ls` (`labelNamesOk`), returns a gauge vector with the variable labels `ls` (`vecLabels`:
what its `WithLabelValues` and `With` need). The vector keeps `s` (its descriptor's
`variableLabels.names`): the slice's points-to is consumed. (mustreg, 2026-11-20) As a collector
(`*GaugeVec`), it describes one descriptor, of `opts`' fully-qualified name (`collectorName`: what
`MustRegister` needs). -/
abbrev prometheus.NewGaugeVec.spec : Prop :=
  ∀ (o : github_com.prometheus.client_golang.prometheus.GaugeOpts) (ns sub name help : GoString)
    (ls : List GoString) (s : GoSlice) (dq : DFrac),
  prometheus.counterOpts o ns sub name help →
  prometheus.nameOk (prometheus.fqName ns sub name) →
  prometheus.labelNamesOk ls →
  {{ (s ↦*{dq} ls : IProp GF) }}
    (App (App (Val (@! github_com.prometheus.client_golang.prometheus.NewGaugeVec)) (Val #o)) (Val #s))
  {{ (v : Loc), RET #v; ⌜prometheus.vecLabels v ls⌝ ∗
      prometheus.collectorName
        (interface.mk (go.GoType.PointerType github_com.prometheus.client_golang.prometheus.GaugeVec.ty) #v)
        (prometheus.fqName ns sub name) }}

end spec

end EtcdGrove
end Perennial
