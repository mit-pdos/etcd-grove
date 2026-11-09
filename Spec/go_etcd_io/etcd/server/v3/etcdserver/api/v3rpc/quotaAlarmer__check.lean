/-
`v3rpc.quotaAlarmer.check` (`server/etcdserver/api/v3rpc/`).

Users: `quotaKVServer.Put`, `quotaKVServer.Txn`, `quotaLeaseServer.LeaseGrant`.

Proof sketch: `newBackendQuota.spec` (a quota over the server's current backend: the fork's fix of `issues/etcd-quota-stale-backend-after-snapshot.md`), its `Available(r)` (2e's `quotaOk`); over the quota, `s.Alarm(ctx, ACTIVATE NOSPACE)` (2c's `EtcdServer.Alarm.spec` for `.alarmActivate`: the server's own environment step, its update built from the `envUpd` the server holds; any outcome) and `ErrGRPCNoSpace`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/quotaAlarmer__check.lean`: no `backendUnderQuota` premise (the refusal is the model's `.noSpace`, a refusal any request may meet).

Margin: whether the request fits the quota is not specified.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3rpc

open Iris Iris.BI EtcdModel EtcdWire ClientV3 Grpc Proto EtcdServer

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `qa.check(ctx, r)` of a request message: `nil`, or `ErrGRPCNoSpace` (the `NOSPACE` alarm
requested). -/
def quotaAlarmer.check.spec : Prop :=
  ∀ (qp : Loc) (qa : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaAlarmer) (s : Loc) (γ : Cluster) (ctx : GoInterface) (t : go.GoType)
    (q : Loc) (dq : DFrac) (c : Content) (gq : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ qp ↦□ qa ∗ quotaAlarmerAt qa s γ ∗ srvGate s gq ∗ Context.ctxOk ctx ∗ msgAt t q dq c ∗ ⌜depth c < depthMax⌝ }}
    (App (App (Val (qp @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaAlarmer.ty @!! go!"check")) (Val #ctx))
      (Val #(msgVal t q)))
  {{ (err : GoInterface), RET #err; msgAt t q dq c ∗ srvGate s gq ∗
      (⌜err = GoInterface.nil⌝ ∨ statusErr err (Rpctypes.code .noSpace) (Rpctypes.desc .noSpace)) }}

end spec

end V3rpc
end EtcdGrove
end Perennial
