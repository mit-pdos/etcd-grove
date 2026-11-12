/-
`v3rpc.authMaintenanceServer.Hash` (`maintenance.go`): the maintenance service's `Hash`,
guarded by the admin guard (`isPermitted`). Lean-first (no Rocq counterpart); the auth plan's A2 (2026-10-23),
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- `ams.Hash(ctx, r)`: the admin guard (`isPermitted`), then the embedded `maintenanceServer`'s `Hash` (names
only, taken as the guarded contract `guardedOk2`: callable only with the token
`adminRes` of the request's auth info); the outcome `guardOut`: the inner call's
answer, or `nil` and an error with `Pin` untouched. -/
abbrev v3rpc.authMaintenanceServer.Hash.spec : Prop :=
  ∀ (p ms aa s : Loc) (E : apply.AEnv GF) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (r : Loc) (Pin : IProp GF)
    (Q : Loc → GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.amsIs p ms aa ∗ v3rpc.authAdminIs aa s E ∗ srvAdminNilOk s E ∗ mvcc.txnCtx ctx cd ∗ E.RD ∗ Pin ∗
      v3rpc.guardedOk2 (adminRes E.authMode) Pin E.RD
        (go.GoType.PointerType v3rpc.maintenanceServer.ty) go!"Hash" ms (GoInterface.ok ctx) r
        Q }}
    (App (App (Val (p @!! go.GoType.PointerType v3rpc.authMaintenanceServer.ty @!! go!"Hash"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); E.RD ∗ v3rpc.guardOut Pin Q resp err }}

end spec

end EtcdGrove
end Perennial
