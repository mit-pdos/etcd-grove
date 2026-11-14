/-
`s.requireAuthInfo(ctx)` (`v3_server.go`): the authenticated-user guard of the server's entry
points (`LeaseGrant`, `LeaseRevoke`, `LeaseTimeToLive`, `MemberList`). Lean-first (no Rocq
counterpart); the auth plan's A2 (2026-10-23), vocabulary `AuthGuard.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthGuard
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthBound
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthWhy
public import Proof.context.LibKeys

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

/-- `s.requireAuthInfo(ctx)`: `nil` unless auth is enabled and the request carries no auth info
(`AuthInfoFromCtx` returned `nil`: `auth.ErrUserEmpty`) or `AuthInfoFromCtx` failed (its error);
the outcome `authedOut` (`AuthGuard.lean`): never an error with auth off, on `nil` the token
`authedRes`, on an error auth enabled at a recorded state. With auth on (the store's request side then bound, `srvAuthAt`'s row), a passed check's auth
info is moreover bound (`authedOutB`, gated by the mode; the auth-mode merge, 2026-10-29: `spec` and
`boundSpec` one spec). Its error is `nil` or one of the auth package's error variables
(`authErrVarIs`: `ErrUserEmpty`, or the store's `ErrInvalidAuthToken`; the lease-expiry plan's E3,
2026-11-05, so that a caller tells it apart from `lease.ErrLeaseNotFound`). -/
abbrev EtcdServer.requireAuthInfo.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvAuthAt s E ∗ mvcc.txnCtx ctx cd ∗ context.libCtxOk ctx ∗ E.RD }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"requireAuthInfo"))
      (Val #(GoInterface.ok ctx)))
  {{ (err : GoInterface), RET #err; E.RD ∗ authedOutB s E.authMode (GoInterface.ok ctx) err ∗
      authErrVarIs err }}

/-- `s.requireAuthInfo(ctx)` with why it refused (auth-guard-completeness G2, 2026-11-14;
`notes/auth-guard-scope.md`, §2.3), for a caller holding a lower bound `n` of the auth store's
published index (`auth.authPubLbM`): `spec`'s post, and on an error the authenticated class's reason
(`authedOutC`'s `authedWhy`): with auth on, `ErrUserEmpty` only when the context carries no token or
auth was disabled at a state no older than `n` (the disable race), `ErrInvalidAuthToken` only for a
token the context carries. So every accepted token passes, whatever its user's roles. -/
abbrev EtcdServer.requireAuthInfo.specC : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (n : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvAuthAt s E ∗ □ auth.authPubLbM E.authMode n ∗ mvcc.txnCtx ctx cd ∗ context.libCtxOk ctx ∗
      E.RD }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"requireAuthInfo"))
      (Val #(GoInterface.ok ctx)))
  {{ (err : GoInterface), RET #err; E.RD ∗ authedOutC s E.authMode n (GoInterface.ok ctx) err ∗
      authErrVarIs err }}

end spec

end EtcdGrove
end Perennial
