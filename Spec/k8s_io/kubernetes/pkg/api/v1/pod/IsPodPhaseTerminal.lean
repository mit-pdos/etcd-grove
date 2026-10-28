/-
`podutil.IsPodPhaseTerminal(phase)` (`pkg/api/v1/pod/util.go:307`): whether `phase` is `Failed` or
`Succeeded`. Lean-first (no Rocq counterpart).
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

/-- **`IsPodPhaseTerminal(p)`** returns `phaseTerminalB p`. -/
abbrev IsPodPhaseTerminal.spec : Prop :=
  ∀ (p : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.api.v1.pod }}
    (App (Val (@! k8s_io.kubernetes.pkg.api.v1.pod.IsPodPhaseTerminal)) (Val #p))
  {{ RET #(phaseTerminalB p); True }}

end spec

end dsctl
end EtcdGrove
end Perennial
