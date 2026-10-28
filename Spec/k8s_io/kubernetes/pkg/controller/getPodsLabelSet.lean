/-
`getPodsLabelSet(template)` (`controller_utils.go:490`): a fresh map holding the template's
labels (empty for none). Lean-first; phase 5 of `notes/k8s-daemonset-plan.md`.
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.PodControlDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI apimodel k8s_io.kubernetes.pkg.controller

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.Assumptions]

/-- **`getPodsLabelSet(tp)`**: a fresh map, owned, of the template's labels (`∅` for none); the
template back. -/
abbrev getPodsLabelSet.spec : Prop :=
  ∀ (tp : Loc) (dq : DFrac) (t : kd.core.PodTemplateSpec),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller ∗ tmplAt tp dq t }}
    (App (Val (@! k8s_io.kubernetes.pkg.controller.getPodsLabelSet)) (Val #tp))
  {{ (m : GoMap), RET #m; m ↦$ (t.ObjectMeta'.Labels'.getD ∅) ∗ tmplAt tp dq t }}

end spec

end dsctl
end EtcdGrove
end Perennial
