/-
`podutil.IsPodReadyConditionTrue(status)` (`pkg/api/v1/pod/util.go:312`): the status's first
`Ready` condition exists and is `True`. Lean-first.
-/
module

public import Proof.k8s_io.kubernetes.pkg.api.v1.pod.Defs

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

/-- **`IsPodReadyConditionTrue(sv)`** on conditions deep-owned with `cs` returns `podReadyB cs`. -/
abbrev IsPodReadyConditionTrue.spec : Prop :=
  ∀ (sv : k8s_io.api.core.v1.PodStatus) (dq : DFrac) (cs : List kd.core.PodCondition),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.api.v1.pod ∗
      ownSliceD kd.core.PodCondition.own sv.Conditions' dq cs }}
    (App (Val (@! k8s_io.kubernetes.pkg.api.v1.pod.IsPodReadyConditionTrue)) (Val #sv))
  {{ RET #(podReadyB cs); ownSliceD (GF := GF) kd.core.PodCondition.own sv.Conditions' dq cs }}

end spec

end dsctl
end EtcdGrove
end Perennial
