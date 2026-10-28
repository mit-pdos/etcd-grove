/-
`podutil.GetPodCondition(status, t)` (`pkg/api/v1/pod/util.go:339`): `GetPodConditionFromList` of
the status's conditions (`(-1, nil)` for a `nil` status; the spec is for a non-`nil` one). Lean-first.
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

/-- **`GetPodCondition(st, t)`** on a status whose conditions are deep-owned with `cs`:
`GetPodConditionFromList`'s result. -/
abbrev GetPodCondition.spec : Prop :=
  ∀ (st : Loc) (dq' : DFrac) (sv : k8s_io.api.core.v1.PodStatus) (dq : DFrac)
    (cs : List kd.core.PodCondition) (t : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.api.v1.pod ∗ st ↦{dq'} sv ∗
      ownSliceD kd.core.PodCondition.own sv.Conditions' dq cs }}
    (App (App (Val (@! k8s_io.kubernetes.pkg.api.v1.pod.GetPodCondition)) (Val #st)) (Val #t))
  {{ (i : w64) (p : Loc), RET (PairV #i #p); st ↦{dq'} sv ∗
      ownSliceD (GF := GF) kd.core.PodCondition.own sv.Conditions' dq cs ∗
      ⌜condResult (sem := sem) sv.Conditions' cs t i p⌝ }}

end spec

end dsctl
end EtcdGrove
end Perennial
