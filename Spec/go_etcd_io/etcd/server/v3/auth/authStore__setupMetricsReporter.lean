/-
`authStore.setupMetricsReporter` (`server/auth/store.go`). Lean-first (no Rocq counterpart); the
auth plan's E2a (2026-10-25), for `NewAuthStore`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.auth auth

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- `as.setupMetricsReporter()`: sets the package's reporter `reportCurrentAuthRev` to a closure
over `as` (its `Revision()`), under the reporter's lock (`reportP`, the package's facts). The
closure runs only from Prometheus's collector, which no verified code calls, so nothing is said of
it. -/
abbrev auth.authStore.setupMetricsReporter.spec : Prop :=
  ∀ (st : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"setupMetricsReporter")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
