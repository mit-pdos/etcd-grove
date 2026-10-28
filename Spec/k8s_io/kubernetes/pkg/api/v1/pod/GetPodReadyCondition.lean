/-
`podutil.GetPodReadyCondition(status)` (`pkg/api/v1/pod/util.go:325`): the address of the status's
first `Ready` condition, or `nil`. Lean-first.
-/
module

public import Spec.k8s_io.kubernetes.pkg.api.v1.pod.GetPodConditionFromList

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
variable [package_sem : k8s_io.kubernetes.pkg.api.v1.pod.Assumptions]

/-- **`GetPodReadyCondition(sv)`** (the status passed by value) on conditions deep-owned with
`cs`: the pointer `GetPodConditionFromList` returns for `Ready`. -/
abbrev GetPodReadyCondition.spec : Prop :=
  ∀ (sv : k8s_io.api.core.v1.PodStatus) (dq : DFrac) (cs : List kd.core.PodCondition),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.api.v1.pod ∗
      ownSliceD kd.core.PodCondition.own sv.Conditions' dq cs }}
    (App (Val (@! k8s_io.kubernetes.pkg.api.v1.pod.GetPodReadyCondition)) (Val #sv))
  {{ (p : Loc), RET #p; ownSliceD (GF := GF) kd.core.PodCondition.own sv.Conditions' dq cs ∗
      ⌜∃ i, condResult (sem := sem) sv.Conditions' cs go!"Ready" i p⌝ }}

end spec

end dsctl
end EtcdGrove
end Perennial
