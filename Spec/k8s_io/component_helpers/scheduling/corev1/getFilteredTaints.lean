/-
`getFilteredTaints(taints, inclusionFilter)` (component-helpers `scheduling/corev1/helpers.go:90`):
the taints the filter keeps, in a new slice (`taints` itself for a `nil` filter; the spec is for
a non-`nil` one, `taintFilterOk`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.component_helpers.scheduling.corev1.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.component_helpers.scheduling.corev1.Assumptions]

/-- **`getFilteredTaints(ts, f)`** with a filter `P` (`taintFilterOk`): a new slice of the
taints `P` keeps (copies of the structs), `ts` kept. -/
abbrev getFilteredTaints.spec : Prop :=
  ∀ (ts : GoSlice) (dq : DFrac) (tvs : List k8s_io.api.core.v1.Taint) (f : GoFunc)
    (P : k8s_io.api.core.v1.Taint → Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.component_helpers.scheduling.corev1 ∗
      ts ↦*{dq} tvs ∗ taintFilterOk f P }}
    (App (App (Val (@! k8s_io.component_helpers.scheduling.corev1.getFilteredTaints)) (Val #ts))
      (Val #f))
  {{ (s : GoSlice), RET #s; ts ↦*{dq} tvs ∗ s ↦* tvs.filter P }}

end spec

end dsctl
end EtcdGrove
end Perennial
