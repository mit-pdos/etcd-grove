/-
`apierrors.HasStatusCause(err, name)` (`k8s.io/apimachinery/pkg/api/errors`, names-only): whether
the error is an `APIStatus` whose details list a cause of type `name`. **A named hypothesis,
boundary pending approval** (the pod control's create and the DaemonSet controller's `syncNodes`
ask it of a create's error with `v1.NamespaceTerminatingCause`; phase 5 of
`notes/k8s-daemonset-plan.md`): `?` in `etc/link-lean-first-k8sdaemon.txt`. Stated weakly: some
boolean (it only reads the error, an immutable value, through `errors.As`).
-/
module

public import Proof.k8s_io.apimachinery.pkg.api.errors.Init

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apierrors

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.api.errors.Assumptions]

/-- `apierrors.HasStatusCause(err, name)`: some boolean. -/
abbrev HasStatusCause.spec : Prop :=
  ∀ (err : GoInterface) (name : k8s_io.apimachinery.pkg.apis.«meta».v1.CauseType),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.errors }}
    (App (App (Val (@! k8s_io.apimachinery.pkg.api.errors.HasStatusCause)) (Val #err)) (Val #name))
  {{ (b : Bool), RET #b; True }}

end spec

end apierrors
end EtcdGrove
end Perennial
