/-
`extractNodeFields(n)` (`nodeaffinity.go:156`): a new `fields.Set` with `metadata.name` for a named
node. Its body is gap D2's named hypothesis (`extractNodeFields_body.lean`). Lean-first.
-/
module

public import Proof.k8s_io.component_helpers.scheduling.corev1.nodeaffinity.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI apimodel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.component_helpers.scheduling.corev1.nodeaffinity.Assumptions]

/-- **`extractNodeFields(n)`** of a node in the heap: a new map, `nodeFieldsM` of its name. -/
abbrev extractNodeFields.spec : Prop :=
  ∀ (n : Loc) (dq : DFrac) (d : kd.core.Node),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.component_helpers.scheduling.corev1.nodeaffinity ∗
      nodeAt n dq d }}
    (App (Val (@! k8s_io.component_helpers.scheduling.corev1.nodeaffinity.extractNodeFields))
      (Val #n))
  {{ (m : Loc), RET #m; nodeAt n dq d ∗ m ↦$ nodeFieldsM d.ObjectMeta'.Name' }}

end spec

end dsctl
end EtcdGrove
end Perennial
