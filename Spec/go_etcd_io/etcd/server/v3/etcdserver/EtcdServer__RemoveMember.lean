/-
`s.RemoveMember(ctx, id)` (`server.go`): a membership operation, guarded by
`checkMembershipOperationPermission`. Lean-first (no Rocq counterpart); the auth plan's A2
(2026-10-23), vocabulary `AuthGuard.lean`.
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

/-- `s.RemoveMember(ctx, id)`: the admin guard, then `mayRemoveMember(id)` (the strict
reconfiguration check) and `configure(ctx, &cc)` with the remove-node configuration change for
`id`; the two callees are names only, taken as contracts (`AuthGuard.lean`): `mayRemoveOk` over
the caller's `Pm`, answering `Qm`; `configureRemoveOk` with the token `adminRes` of the request's
auth info, over the caller's `Pin`, answering `Qin`. The result is `configure`'s, or an error with
`Pin` kept (the guard's error, `applyErrIs`, or the check's `Qm err`). -/
abbrev EtcdServer.RemoveMember.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (id : w64) (Pin Pm : IProp GF) (Qm : GoInterface → IProp GF)
    (Qin : GoSlice → GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvAuthAt s E ∗ srvAdminNilOk s E ∗ mvcc.txnCtx ctx cd ∗ E.RD ∗ Pin ∗ Pm ∗
      mayRemoveOk s id Pm Qm ∗ configureRemoveOk s E ctx id Pin Qm Qin }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"RemoveMember"))
      (Val #(GoInterface.ok ctx))) (Val #id))
  {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err); E.RD ∗
      (Qin sl err ∨ (⌜err ≠ GoInterface.nil⌝ ∗ Pin ∗ ((applyErrIs err ∗ Pm) ∨ Qm err))) }}

end spec

end EtcdGrove
end Perennial
