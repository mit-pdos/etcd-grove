/-
`v3rpc.authMaintenanceServer.Status` (`maintenance.go`): the maintenance service's `Status`,
guarded by the authenticated-user guard (`requireAuthInfo`). Lean-first (no Rocq counterpart); the auth plan's A2 (2026-10-23),
vocabulary `v3rpc/InvAuthAdmin.lean`.
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

/-- `ams.Status(ctx, r)`: the authenticated-user guard (`requireAuthInfo`), then the embedded `maintenanceServer`'s `Status` (names
only, taken as the guarded contract `guardedOk2`: callable only with the token
`authedRes` of the request's auth info); the outcome `guardOut`: the inner call's
answer, or `nil` and an error with `Pin` untouched. -/
abbrev v3rpc.authMaintenanceServer.Status.spec : Prop :=
  ∀ (p ms aa s : Loc) (E : apply.AEnv GF) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (r : Loc) (Pin : IProp GF)
    (Q : Loc → GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.amsIs p ms aa ∗ v3rpc.authAdminIs aa s E ∗ mvcc.txnCtx ctx cd ∗ E.RD ∗ Pin ∗
      v3rpc.guardedOk2 (authedRes E.authMode) Pin E.RD
        (go.GoType.PointerType v3rpc.maintenanceServer.ty) go!"Status" ms (GoInterface.ok ctx) r
        Q }}
    (App (App (Val (p @!! go.GoType.PointerType v3rpc.authMaintenanceServer.ty @!! go!"Status"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); E.RD ∗ v3rpc.guardOut Pin Q resp err }}

end spec

end EtcdGrove
end Perennial
