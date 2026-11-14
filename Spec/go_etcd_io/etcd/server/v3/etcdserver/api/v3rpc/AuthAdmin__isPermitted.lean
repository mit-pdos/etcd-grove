/-
`v3rpc.AuthAdmin.isPermitted` (`auth.go`): the admin guard of the gRPC services (`Compact`, the
maintenance operations). Lean-first (no Rocq counterpart); the auth plan's A2 (2026-10-23),
vocabulary `v3rpc/InvAuthAdmin.lean` and `etcdserver/AuthGuard.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvAuthAdmin
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

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- `aa.isPermitted(ctx)`: the getter's `AuthInfoFromCtx`, then its store's `IsAdminPermitted`
on the answer (`nil` or not: `srvAdminNilOk`, the premise `AuthGuard.lean` describes); the
outcome `adminOut`: on `nil` the token `adminRes` for the request's auth info.
With auth on, a passed check's auth info is moreover bound (`adminOutB`; the auth-mode merge,
2026-10-29: `spec` and `boundSpec` one spec). -/
abbrev v3rpc.AuthAdmin.isPermitted.spec : Prop :=
  ∀ (aa s : Loc) (E : apply.AEnv GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.authAdminIs aa s E ∗ srvAdminNilOk s E ∗ mvcc.txnCtx ctx cd ∗ context.libCtxOk ctx ∗ E.RD }}
    (App (Val (aa @!! go.GoType.PointerType v3rpc.AuthAdmin.ty @!! go!"isPermitted"))
      (Val #(GoInterface.ok ctx)))
  {{ (err : GoInterface), RET #err; E.RD ∗ adminOutB s E.authMode (GoInterface.ok ctx) err }}

/-- `aa.isPermitted(ctx)` with why it refused (auth-guard-completeness G2, 2026-11-14), for a caller
holding a lower bound `n` of the auth store's published index: `spec`'s post, and on an error the
admin class's reason (`adminOutC`, as `EtcdServer.checkMembershipOperationPermission.specC`);
`srvAdminNilOk` is not a premise (`authAdminIs`'s `srvAuthAt` gives it). -/
abbrev v3rpc.AuthAdmin.isPermitted.specC : Prop :=
  ∀ (aa s : Loc) (E : apply.AEnv GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (n : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.authAdminIs aa s E ∗ □ auth.authPubLbM E.authMode n ∗ mvcc.txnCtx ctx cd ∗
      context.libCtxOk ctx ∗ E.RD }}
    (App (Val (aa @!! go.GoType.PointerType v3rpc.AuthAdmin.ty @!! go!"isPermitted"))
      (Val #(GoInterface.ok ctx)))
  {{ (err : GoInterface), RET #err; E.RD ∗ adminOutC s E.authMode n (GoInterface.ok ctx) err }}

end spec

end EtcdGrove
end Perennial
