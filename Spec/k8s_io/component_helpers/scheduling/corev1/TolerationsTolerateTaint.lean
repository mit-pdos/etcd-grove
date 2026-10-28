/-
`v1helper.TolerationsTolerateTaint(logger, tolerations, taint, enableComparisonOperators)`
(component-helpers `scheduling/corev1/helpers.go:68`): whether some toleration tolerates the taint
(`Toleration.ToleratesTaint`, a boundary). Lean-first (no Rocq counterpart).
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

/-- **`TolerationsTolerateTaint(logger, ts, n, en)`** on a slice of tolerations and a taint (both
read): some `bool`, `false` when there is no toleration. -/
abbrev TolerationsTolerateTaint.spec : Prop :=
  ∀ (logger : github_com.go_logr.logr.Logger) (ts : GoSlice) (dq : DFrac)
    (tols : List k8s_io.api.core.v1.Toleration) (n : Loc) (dq' : DFrac)
    (nv : k8s_io.api.core.v1.Taint) (en : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.component_helpers.scheduling.corev1 ∗
      ts ↦*{dq} tols ∗ n ↦{dq'} nv }}
    (App (App (App (App (Val (@! k8s_io.component_helpers.scheduling.corev1.TolerationsTolerateTaint))
      (Val #logger)) (Val #ts)) (Val #n)) (Val #en))
  {{ (b : Bool), RET #b; ts ↦*{dq} tols ∗ n ↦{dq'} nv ∗ ⌜tols = [] → b = false⌝ }}

end spec

end dsctl
end EtcdGrove
end Perennial
