/-
`s.checkMembershipOperationPermission(ctx)` (`server.go`): the admin guard of the membership
operations (`AddMember`, `RemoveMember`, `UpdateMember`, `promoteMember`). Lean-first (no Rocq
counterpart); the auth plan's A2 (2026-10-23), vocabulary `AuthGuard.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthGuard
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthBound

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.checkMembershipOperationPermission(ctx)`: `AuthInfoFromCtx`, then the store's
`IsAdminPermitted` on its answer (`nil` or not: `srvAdminNilOk`, the premise `AuthGuard.lean`
describes); the outcome `adminOut`: on `nil` the token `adminRes` for the request's auth info.
(The `s.authStore == nil` branch is for tests: the server's store is an interface value,
`isReqAuth`.) With auth on (the store's request side then bound, `srvAuthAt`'s row), a passed check's auth
info is moreover bound to the request's token or came from the TLS fallback (`adminOutB`, gated by
the mode; the auth-mode merge, 2026-10-29: `spec` and `boundSpec` one spec). -/
abbrev EtcdServer.checkMembershipOperationPermission.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvAuthAt s E ∗ srvAdminNilOk s E ∗ mvcc.txnCtx ctx cd ∗ E.RD }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!!
      go!"checkMembershipOperationPermission")) (Val #(GoInterface.ok ctx)))
  {{ (err : GoInterface), RET #err; E.RD ∗ adminOutB s E.authMode (GoInterface.ok ctx) err }}

end spec

end EtcdGrove
end Perennial
