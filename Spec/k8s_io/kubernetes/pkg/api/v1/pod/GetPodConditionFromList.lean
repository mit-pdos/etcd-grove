/-
`podutil.GetPodConditionFromList(conditions, t)` (`pkg/api/v1/pod/util.go:348`): the index of the
first condition of type `t` and its address in the slice, or `(-1, nil)`. Lean-first.
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

/-- **The result of `GetPodConditionFromList(s, t)`** on a slice holding `cs`: `(-1, nil)` if no
condition has type `t`, else the first one's index `j` and address (`&s[j]`). -/
def condResult (s : GoSlice) (cs : List kd.core.PodCondition) (t : GoString) (i : w64) (p : Loc) :
    Prop :=
  match condFind cs t with
  | none => i = W64 (-1) ∧ p = null
  | some (j, _) => i = W64 j ∧ p = sliceIndexRef k8s_io.api.core.v1.PodCondition (j : Int) s

/-- **`GetPodConditionFromList(s, t)`** on a slice deep-owned with `cs` returns `condResult`. -/
abbrev GetPodConditionFromList.spec : Prop :=
  ∀ (s : GoSlice) (dq : DFrac) (cs : List kd.core.PodCondition) (t : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.api.v1.pod ∗
      ownSliceD kd.core.PodCondition.own s dq cs }}
    (App (App (Val (@! k8s_io.kubernetes.pkg.api.v1.pod.GetPodConditionFromList)) (Val #s)) (Val #t))
  {{ (i : w64) (p : Loc), RET (PairV #i #p); ownSliceD (GF := GF) kd.core.PodCondition.own s dq cs ∗
      ⌜condResult (sem := sem) s cs t i p⌝ }}

end spec

end dsctl
end EtcdGrove
end Perennial
