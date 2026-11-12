/-
`v3rpc.authMaintenanceServer.Snapshot` (`maintenance.go`): the maintenance service's `Snapshot`
(a stream handler), guarded by the admin guard on the stream's context. Lean-first (no Rocq
counterpart); the auth plan's A2 (2026-10-23), vocabulary `v3rpc/InvAuthAdmin.lean`.
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

/-- `ams.Snapshot(sr, srv)`: `isPermitted(srv.Context())` (the stream's context,
`streamCtxOk`, names only), then the embedded `maintenanceServer`'s `Snapshot` (names only, the
guarded contract `guardedSnapOk` with the token `adminRes`); the outcome `guardOut1`: the inner
call's error, or an error with `Pin` untouched. -/
abbrev v3rpc.authMaintenanceServer.Snapshot.spec : Prop :=
  ∀ (p ms aa s : Loc) (E : apply.AEnv GF) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (sr : Loc) (srv : GoInterface) (Pin : IProp GF)
    (Q : GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.amsIs p ms aa ∗ v3rpc.authAdminIs aa s E ∗ srvAdminNilOk s E ∗ mvcc.txnCtx ctx cd ∗
      E.RD ∗ Pin ∗ v3rpc.streamCtxOk srv ctx ∗
      v3rpc.guardedSnapOk (adminRes E.authMode) Pin E.RD ms sr srv Q }}
    (App (App (Val (p @!! go.GoType.PointerType v3rpc.authMaintenanceServer.ty @!! go!"Snapshot"))
      (Val #sr)) (Val #srv))
  {{ (err : GoInterface), RET #err; E.RD ∗ v3rpc.guardOut1 Pin Q err }}

end spec

end EtcdGrove
end Perennial
