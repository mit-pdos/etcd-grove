/-
`historiesByRevision.Len()` (`update.go:630`): the slice's length. Lean-first; Stage 3, track B.
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

/-- **`historiesByRevision(s).Len()`**. -/
abbrev historiesByRevision.Len.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (xs : List kd.apps.ControllerRevision),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller.daemon ∗ crsAt sl dq xs }}
    (App (Val #(methods historiesByRevision.ty go!"Len" #sl)) (Val #()))
  {{ RET #(W64 xs.length); crsAt sl dq xs }}

end spec

end dsctl
end EtcdGrove
end Perennial
