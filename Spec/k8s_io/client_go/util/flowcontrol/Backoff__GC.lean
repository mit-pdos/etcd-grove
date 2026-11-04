/-
`(*flowcontrol.Backoff).GC()` (with body): under the lock, deletes the entries whose last update
is older than twice the maximum duration. Lean-first, track C of the DaemonSet run.
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.daemon.LifeDefs

@[expose] public section

set_option autoImplicit false

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
variable [fc_sem : k8s_io.client_go.util.flowcontrol.Assumptions]

/-- `b.GC()`: returns. -/
abbrev flowcontrol.Backoff.GC.spec : Prop :=
  ∀ (b : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.flowcontrol ∗ isBackoff b }}
    (App (Val (b @!! go.GoType.PointerType k8s_io.client_go.util.flowcontrol.Backoff.ty @!! go!"GC"))
      (Val #()))
  {{ RET #(); True }}

end spec

end dsctl
end EtcdGrove
end Perennial
