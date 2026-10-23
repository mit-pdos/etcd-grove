/-
`v3rpc.authMaintenanceServer.Alarm` (`maintenance.go`): the maintenance service's `Alarm`,
guarded by the authenticated-user guard for a get (`AlarmRequest_GET`) and the admin guard
otherwise. Lean-first (no Rocq counterpart); the auth plan's A2 (2026-10-23), vocabulary
`v3rpc/InvAuthAdmin.lean`.
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

/-- `ams.Alarm(ctx, ar)`: `requireAuthInfo` when `ar.GetAction()` (`alarmActionOk`, names only)
is `AlarmRequest_GET`, `isPermitted` otherwise, then the embedded `maintenanceServer`'s `Alarm`
(names only, the guarded contract `guardedOk2` with the token `alarmTok` of the action); the
outcome `guardOut`. -/
abbrev v3rpc.authMaintenanceServer.Alarm.spec : Prop :=
  ∀ (p ms aa s : Loc) (E : apply.AEnv GF) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (ar : Loc) (act : w32) (Pin : IProp GF)
    (Q : Loc → GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.amsIs p ms aa ∗ v3rpc.authAdminIs aa s E ∗ srvAdminNilOk s E ∗ mvcc.txnCtx ctx cd ∗
      E.RD ∗ Pin ∗ v3rpc.alarmActionOk ar act ∗
      v3rpc.guardedOk2 (v3rpc.alarmTok E.authMode act) Pin E.RD
        (go.GoType.PointerType v3rpc.maintenanceServer.ty) go!"Alarm" ms (GoInterface.ok ctx) ar
        Q }}
    (App (App (Val (p @!! go.GoType.PointerType v3rpc.authMaintenanceServer.ty @!! go!"Alarm"))
      (Val #(GoInterface.ok ctx))) (Val #ar))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); E.RD ∗ v3rpc.guardOut Pin Q resp err }}

end spec

end EtcdGrove
end Perennial
