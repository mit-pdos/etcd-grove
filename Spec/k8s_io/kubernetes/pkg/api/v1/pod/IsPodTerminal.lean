/-
`podutil.IsPodTerminal(pod)` (`pkg/api/v1/pod/util.go:302`): the pod's phase is `Failed` or
`Succeeded`. Lean-first.
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
/-- **`IsPodTerminal(pod)`** of a pod in the heap returns `phaseTerminalB` of its phase. -/
abbrev IsPodTerminal.spec : Prop :=
  ∀ (pod : Loc) (dq : DFrac) (d : kd.core.Pod),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.api.v1.pod ∗ podAt pod dq d }}
    (App (Val (@! k8s_io.kubernetes.pkg.api.v1.pod.IsPodTerminal)) (Val #pod))
  {{ RET #(phaseTerminalB d.Status'.Phase'); podAt pod dq d }}

end spec

end dsctl
end EtcdGrove
end Perennial
