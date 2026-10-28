/-
`isExpiredError(err)` (`reflector.go:1154`): `apierrors.IsResourceExpired(err) ||
apierrors.IsGone(err)`. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md`, fifth round. Stated
as its callees (named hypotheses, pending approval) are: some boolean.
-/
module

public import Proof.k8s_io.client_go.tools.cache.CacheDefs

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

/-- **`isExpiredError(err)`**: some boolean. -/
abbrev isExpiredError.spec : Prop :=
  ∀ (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache }}
    (App (Val (@! k8s_io.client_go.tools.cache.isExpiredError)) (Val #err))
  {{ (b : Bool), RET #b; True }}

end spec

end cache
end EtcdGrove
end Perennial
