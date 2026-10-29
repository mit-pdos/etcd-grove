/-
`v1helper.FindMatchingUntoleratedTaint(logger, taints, tolerations, inclusionFilter,
enableComparisonOperators)` (component-helpers `scheduling/corev1/helpers.go:79`): the first taint
the filter keeps that no toleration tolerates, and whether there is one. Lean-first.
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

/-- **`FindMatchingUntoleratedTaint(logger, ns, ts, f, en)`** with a filter `P`
(`taintFilterOk`): `(n, b)` where `b` is whether some kept taint is untolerated (whether a
toleration tolerates a taint is a boundary: some `bool`), so `false` if the filter keeps no taint
and, with no toleration, `true` exactly when it keeps one; a `true` comes with a kept taint. -/
abbrev FindMatchingUntoleratedTaint.spec : Prop :=
  ∀ (logger : github_com.go_logr.logr.Logger) (ns : GoSlice) (dq : DFrac)
    (nvs : List k8s_io.api.core.v1.Taint) (ts : GoSlice) (dq' : DFrac)
    (tols : List k8s_io.api.core.v1.Toleration) (f : GoFunc)
    (P : k8s_io.api.core.v1.Taint → Bool) (en : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.component_helpers.scheduling.corev1 ∗
      ns ↦*{dq} nvs ∗ ts ↦*{dq'} tols ∗ taintFilterOk f P }}
    (App (App (App (App (App (Val (@! k8s_io.component_helpers.scheduling.corev1.FindMatchingUntoleratedTaint))
      (Val #logger)) (Val #ns)) (Val #ts)) (Val #f)) (Val #en))
  {{ (n : k8s_io.api.core.v1.Taint) (b : Bool), RET (PairV #n #b); ns ↦*{dq} nvs ∗ ts ↦*{dq'} tols ∗
      ⌜(nvs.filter P = [] → b = false) ∧ (tols = [] → b = !(nvs.filter P).isEmpty) ∧
        (b = true → n ∈ nvs.filter P)⌝ }}

end spec

end dsctl
end EtcdGrove
end Perennial
