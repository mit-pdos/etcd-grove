/-
`apierrors.IsResourceExpired(err)` (`k8s.io/apimachinery/pkg/api/errors`, names-only): whether the
error's status reason is `Expired`. **A named hypothesis, boundary pending approval** (one of the
`apierrors` predicates the reflector's `list` and `watch` call; phase 4 of
`notes/k8s-daemonset-plan.md`, fifth round): `?` in `etc/link-lean-first-k8scache.txt`. Stated
weakly: some boolean, which is all the reflector's partial correctness needs (each branch keeps
the informer's contract).
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.api.errors.Assumptions]

/-- `apierrors.IsResourceExpired(err)`: some boolean. -/
abbrev IsResourceExpired.spec : Prop :=
  ∀ (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.errors }}
    (App (Val (@! k8s_io.apimachinery.pkg.api.errors.IsResourceExpired)) (Val #err))
  {{ (b : Bool), RET #b; True }}

end spec

end apierrors
end EtcdGrove
end Perennial
