/-
`s.requireAuthInfo(ctx)` (`v3_server.go`): the authenticated-user guard of the server's entry
points (`LeaseGrant`, `LeaseRevoke`, `LeaseTimeToLive`, `MemberList`). Lean-first (no Rocq
counterpart); the auth plan's A2 (2026-10-23), vocabulary `AuthGuard.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthGuard

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
`authedRes`, on an error auth enabled at a recorded state. -/
abbrev EtcdServer.requireAuthInfo.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvAuthAt s E ∗ mvcc.txnCtx ctx cd ∗ E.RD }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"requireAuthInfo"))
      (Val #(GoInterface.ok ctx)))
  {{ (err : GoInterface), RET #err; E.RD ∗ authedOut E.authMode err }}

end spec

end EtcdGrove
end Perennial
