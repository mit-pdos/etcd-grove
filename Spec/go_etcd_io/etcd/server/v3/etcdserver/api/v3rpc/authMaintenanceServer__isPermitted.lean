/-
`v3rpc.authMaintenanceServer.isPermitted` (`maintenance.go`): the embedded `*AuthAdmin`'s
`isPermitted`, promoted. Lean-first (no Rocq counterpart); the auth plan's A2 (2026-10-23).
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

/-- `ams.isPermitted(ctx)`: `ams.AuthAdmin.isPermitted(ctx)` (`AuthAdmin__isPermitted.lean`). -/
abbrev v3rpc.authMaintenanceServer.isPermitted.spec : Prop :=
  ∀ (p ms aa s : Loc) (E : apply.AEnv GF) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.amsIs p ms aa ∗ v3rpc.authAdminIs aa s E ∗ srvAdminNilOk s E ∗ mvcc.txnCtx ctx cd ∗
      E.RD }}
    (App (Val (p @!! go.GoType.PointerType v3rpc.authMaintenanceServer.ty @!! go!"isPermitted"))
      (Val #(GoInterface.ok ctx)))
  {{ (err : GoInterface), RET #err; E.RD ∗ adminOut E.authMode err }}

end spec

end EtcdGrove
end Perennial
