/-
`(*EtcdServer).monitorStorageVersion()` (`server.go`): the trust boundary (names-only; one of the goroutines `Start`
attaches). Lean-first (the request path's unit 4c; restated 2026-10-18, D19i part 2).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvStorageVersion

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.monitorStorageVersion()` returns (names-only: the storage version monitor, until
`stopping`). It migrates the backend's storage version (`meta/storageVersion`) under
`LockOutsideApply` with the resources `srvSVRes` gives (`InvStorageVersion.lean`): the server's
backend for good, its contract, a read token with an open share, and the write budget it shares
with the apply thread (one write-back token per `Unlock`, for a time receipt). True of the fork's
code (`issues/etcd-backend-duplicate-put-stale-read.md`: the migration may put the key several
times in one session). Until 2026-10-18 (D19i part 2) the contract took only the package's
initialization, false: the monitor wrote the backend without its resources (`notes/audit.md`). -/
abbrev EtcdServer.monitorStorageVersion.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γp : GName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ srvSVRes s E.γ ∗ srvWTPool E.γ γp }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"monitorStorageVersion")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
