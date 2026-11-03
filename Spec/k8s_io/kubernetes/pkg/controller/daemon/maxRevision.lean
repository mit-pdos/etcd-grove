/-
`maxRevision(histories)` (`update.go:399`): the largest revision, `0` for none. Lean-first;
Stage 3, track B.
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.daemon.SyncDefs

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI apimodel consistency k8s_io.kubernetes.pkg.controller.daemon

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.daemon.Assumptions]

/-- **`maxRevision(hl)`**: `maxRevD rs`. -/
abbrev maxRevision.spec : Prop :=
  ∀ (hl : GoSlice) (dq : DFrac) (rs : List kd.apps.ControllerRevision),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller.daemon ∗ crsAt hl dq rs }}
    (App (Val (@! k8s_io.kubernetes.pkg.controller.daemon.maxRevision)) (Val #hl))
  {{ RET #(maxRevD rs); crsAt hl dq rs }}

end spec

end dsctl
end EtcdGrove
end Perennial
