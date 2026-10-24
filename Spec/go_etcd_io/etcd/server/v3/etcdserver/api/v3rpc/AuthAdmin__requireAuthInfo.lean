/-
`v3rpc.AuthAdmin.requireAuthInfo` (`auth.go`): the authenticated-user guard of the gRPC services
(the maintenance `Status`, `Alarm` get). Lean-first (no Rocq counterpart); the auth plan's A2
(2026-10-23), vocabulary `v3rpc/InvAuthAdmin.lean` and `etcdserver/AuthGuard.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvAuthAdmin

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- `aa.requireAuthInfo(ctx)`: `nil` unless auth is enabled and the request carries no auth info
(`auth.ErrUserEmpty`) or the getter's `AuthInfoFromCtx` failed; the outcome `authedOut`
(`AuthGuard.lean`): never an error with auth off, on `nil` the token `authedRes`, on an error
auth enabled at a recorded state. -/
abbrev v3rpc.AuthAdmin.requireAuthInfo.spec : Prop :=
  ∀ (aa s : Loc) (E : apply.AEnv GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.authAdminIs aa s E ∗ mvcc.txnCtx ctx cd ∗ E.RD }}
    (App (Val (aa @!! go.GoType.PointerType v3rpc.AuthAdmin.ty @!! go!"requireAuthInfo"))
      (Val #(GoInterface.ok ctx)))
  {{ (err : GoInterface), RET #err; E.RD ∗ authedOut E.authMode err }}

end spec

end EtcdGrove
end Perennial
