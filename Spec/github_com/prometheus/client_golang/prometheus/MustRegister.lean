/-
prometheus's `MustRegister(cs...)` (names only; item 8, the read package's initializer):
registering one collector of a name whose right the caller holds does not panic.
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

/-- `prometheus.MustRegister(c)` of one collector `c` describing one label-free descriptor named
`n` returns, given the right to register `n` (`nameFree n`, consumed: the name is registered). -/
abbrev prometheus.MustRegister.spec : Prop :=
  ∀ (s : GoSlice) (dq : DFrac) (c : GoInterfaceOk) (n : GoString),
  prometheus.collectorName c n →
  {{ s ↦*{dq} [GoInterface.ok c] ∗ prometheus.nameFree (GF := GF) n }}
    (App (Val (@! github_com.prometheus.client_golang.prometheus.MustRegister)) (Val #s))
  {{ RET #(); s ↦*{dq} [GoInterface.ok c] }}

end spec

end EtcdGrove
end Perennial
