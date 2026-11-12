/-
`podutil.IsPodReady(pod)` (`pkg/api/v1/pod/util.go:297`): the pod's first `Ready` condition is
`True`. Lean-first.
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

open apimodel in
/-- **`IsPodReady(pod)`** of a pod in the heap returns `podReadyB` of its conditions. -/
abbrev IsPodReady.spec : Prop :=
  ∀ (pod : Loc) (dq : DFrac) (d : kd.core.Pod),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.api.v1.pod ∗ podAt pod dq d }}
    (App (Val (@! k8s_io.kubernetes.pkg.api.v1.pod.IsPodReady)) (Val #pod))
  {{ RET #(podReadyB d.Status'.Conditions'); podAt pod dq d }}

end spec

end dsctl
end EtcdGrove
end Perennial
