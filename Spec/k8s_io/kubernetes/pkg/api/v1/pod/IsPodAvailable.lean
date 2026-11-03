/-
`podutil.IsPodAvailable(pod, minReadySeconds, now)` (`pkg/api/v1/pod/util.go`): the pod is ready
and has been for `minReadySeconds`. Lean-first; Stage 3, track B (the rolling update and the status
counters). Any boolean; the pod comes back.
-/
module

public import Proof.k8s_io.kubernetes.pkg.api.v1.pod.Defs

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI apimodel consistency 

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.api.v1.pod.Assumptions]

/-- **`IsPodAvailable(p, mrs, now)`**: some boolean. -/
abbrev IsPodAvailable.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (d : kd.core.Pod) (mrs : w32)
    (now : k8s_io.apimachinery.pkg.apis.«meta».v1.Time),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.api.v1.pod ∗ podAt p dq d }}
    (App (App (App (Val (@! k8s_io.kubernetes.pkg.api.v1.pod.IsPodAvailable)) (Val #p)) (Val #mrs)) (Val #now))
  {{ (b : Bool), RET #b; podAt p dq d }}

end spec

end dsctl
end EtcdGrove
end Perennial
