/-
prometheus's `MustRegister(cs...)` (client_golang v1.24.1, `registry.go:176`, translated with its body:
`DefaultRegisterer.MustRegister(cs...)`; route (b), notes/prom-registry.md) of one collector describing
one descriptor (a metric or a metric vector: `collectorName`), given the right to its ID: it returns.
(Until 2026-11-22 names only, a trust-boundary axiom over the right `nameFree n`.)
-/
module

public import Proof.github_com.prometheus.client_golang.prometheus.PkgInit

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

/-- `prometheus.MustRegister(c)` of one collector `c` describing one descriptor named `n` (no built-in
collector's name), without const labels (`collectorName`: its ID `descId n`), returns, given prometheus's
fact and the right to `descId n` at the run's registry name (`PromRegGS`, the fact's parameter; the
right is consumed: the ID is registered). The slice is read at any fraction and kept. -/
abbrev prometheus.MustRegister.spec : Prop :=
  ∀ [promreg_gs : prometheus.PromRegGS GF] (s : GoSlice) (dq : DFrac) (c : GoInterfaceOk) (n : GoString),
  n ∉ prometheus.builtinNames →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus ∗
      s ↦*{dq} [GoInterface.ok c] ∗ prometheus.collectorName c n ∗
      prometheus.idToks (prometheus.PromRegGS.γ (GF := GF)) [prometheus.descId n] }}
    (App (Val (@! github_com.prometheus.client_golang.prometheus.MustRegister)) (Val #s))
  {{ RET #(); s ↦*{dq} [GoInterface.ok c] }}

end spec

end EtcdGrove
end Perennial
