/-
`isTooLargeResourceVersionError(err)` (`reflector.go:1162`): whether the error's status has the
cause `ResourceVersionTooLarge`, or is a timeout whose message says the version is too large.
**Pending** (specified, not proved this round; `?` in `etc/link-lean-first-k8scache.txt`): its
`err.(apierrors.APIStatus)` assertion and `apierr.Status()` need the error's dynamic type's method
set and the API errors' methods (names-only). Lean-first; phase 4 of `notes/k8s-daemonset-plan.md`,
fifth round. Stated as the reflector's `list` needs it: some boolean.
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

/-- **`isTooLargeResourceVersionError(err)`**: some boolean. -/
abbrev isTooLargeResourceVersionError.spec : Prop :=
  ∀ (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache }}
    (App (Val (@! k8s_io.client_go.tools.cache.isTooLargeResourceVersionError)) (Val #err))
  {{ (b : Bool), RET #b; True }}

end spec

end cache
end EtcdGrove
end Perennial
