/-
prometheus's `MustRegister(cs...)` (names only; item 8, the read package's initializer):
registering one collector of a name whose right the caller holds does not panic.
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

/-- `prometheus.MustRegister(c)` of one collector `c` describing one descriptor named `n` without
const labels (a metric, or a metric vector: `collectorName`) returns, given the right to register `n`
(`regFree n`, consumed: the name is registered; prom-registry, 2026-11-22: until then the axiom
`nameFree n`) and prometheus's initialization (its default registry). -/
abbrev prometheus.MustRegister.spec : Prop :=
  ∀ (s : GoSlice) (dq : DFrac) (c : GoInterfaceOk) (n : GoString),
  prometheus.collectorName c n →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus ∗
      s ↦*{dq} [GoInterface.ok c] ∗ prometheus.regFree (GF := GF) n }}
    (App (Val (@! github_com.prometheus.client_golang.prometheus.MustRegister)) (Val #s))
  {{ RET #(); s ↦*{dq} [GoInterface.ok c] }}

end spec

end EtcdGrove
end Perennial
