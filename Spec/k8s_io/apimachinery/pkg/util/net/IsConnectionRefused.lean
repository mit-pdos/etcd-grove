/-
`utilnet.IsConnectionRefused(err)` (`k8s.io/apimachinery/pkg/util/net`, names-only): whether the
error wraps `ECONNREFUSED`. **A named hypothesis** (outside client-go, no axiom this round; the
reflector's `isWatchErrorRetriable` calls it; phase 4 of `notes/k8s-daemonset-plan.md`, fifth
round): `?` in `etc/link-lean-first-k8scache.txt`. Stated weakly: some boolean.
-/
module

public import Proof.k8s_io.apimachinery.pkg.util.net.Init

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.util.net.Assumptions]

/-- `utilnet.IsConnectionRefused(err)`: some boolean. -/
abbrev net.IsConnectionRefused.spec : Prop :=
  ∀ (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.net }}
    (App (Val (@! k8s_io.apimachinery.pkg.util.net.IsConnectionRefused)) (Val #err))
  {{ (b : Bool), RET #b; True }}

end spec

end EtcdGrove
end Perennial
