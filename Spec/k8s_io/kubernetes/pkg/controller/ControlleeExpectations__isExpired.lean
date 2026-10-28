/-
`(*ControlleeExpectations).isExpired()` (`controller_utils.go:232`): whether the real clock's
time since the timestamp exceeds `ExpectationsTimeout`. Lean-first; phase 5 of `notes/k8s-daemonset-plan.md`.
-/
module

public import Proof.k8s_io.kubernetes.Base
public import Proof.k8s_io.kubernetes.pkg.controller.ExpDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI k8s_io.kubernetes.pkg.controller

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.Assumptions]

/-- **`e.isExpired()`**: some boolean (the clock is not modeled). -/
abbrev ControlleeExpectations.isExpired.spec : Prop :=
  ∀ (e : Loc) (k : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller ∗ isCE e k }}
    (App (Val (e @!! go.GoType.PointerType ControlleeExpectations.ty @!! go!"isExpired")) (Val #()))
  {{ (b : Bool), RET #b; True }}

end spec

end dsctl
end EtcdGrove
end Perennial
