/-
`isWatchErrorRetriable(err)` (`reflector.go:1195`): `utilnet.IsConnectionRefused(err) ||
apierrors.IsTooManyRequests(err)`. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md`, fifth round. Stated
as its callees (named hypotheses, pending approval) are: some boolean. Precondition
`apierrors.apiErrOk err` or `nil`, which its callees need (apierrors-fix, 2026-11-17: on a typed-nil
`*StatusError` they panic, `notes/apierrors-typednil-hypotheses.md`).
-/
module

public import Proof.k8s_io.client_go.tools.cache.CacheDefs
public import Proof.k8s_io.apimachinery.pkg.api.errors.View

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **`isWatchErrorRetriable(err)`** of `nil` or an error `apierrors`' checks may read: some boolean. -/
abbrev isWatchErrorRetriable.spec : Prop :=
  ∀ (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗
      (⌜err = interface.nil⌝ ∨ apierrors.apiErrOk err) }}
    (App (Val (@! k8s_io.client_go.tools.cache.isWatchErrorRetriable)) (Val #err))
  {{ (b : Bool), RET #b; True }}

end spec

end cache
end EtcdGrove
end Perennial
