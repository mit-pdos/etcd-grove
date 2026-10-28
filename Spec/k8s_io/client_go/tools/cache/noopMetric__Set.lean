/-
`noopMetric.Set(float64)` (`reflector_metrics.go:54`): does nothing. Lean-first.
-/
module

public import Proof.k8s_io.client_go.tools.cache.TSDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- `m.Set(x)`: returns. -/
abbrev noopMetric.Set.spec : Prop :=
  ∀ (m : noopMetric) (x : w64),
  {{ (True : IProp GF) }}
    (App (Val (m @!! noopMetric.ty @!! go!"Set")) (Val #x))
  {{ RET #(); True }}

end spec

end cache
end EtcdGrove
end Perennial
